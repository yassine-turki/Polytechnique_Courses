import math

alpha_over2= [math.cos((i/16)*math.pi)/2 for i in range(8)] 

 
def ppm_tokenize(stream):
    """Takes an input stream and that returns an iterator for all the tokens of stream, 
    ignoring the comments
    """
    for line in stream:
        for element in line.split():
            if element[0]=="#":
                break
            else:
                yield element
        


def ppm_load(stream):
    """Takes an input stream and loads the PPM image, 
    returning the resulting image as a 3-element tuple (w, h, img) ,
    where w is the image’s width, h is the image’s height and img is a 2D-array 
    that contains the image’s pixels’ color information
    """
    
    gen = ppm_tokenize(stream)
    
    #Format handling

    p3 = next(gen)
    if p3 != 'P3':
        print('Wrong ppm format', p3)
        return None

    w, h = int(next(gen)), int(next(gen))
    if w == 0 or h == 0 :
        print('Wrong widht / height format', w, h)
        return None
    
    color_size = int(next(gen))
    if color_size != 255:
        print('Wrong color_size format', color_size)
        return None
    
    #Data Processing
    
    img=[]
    for _ in range(h):
        l=[]
        for _ in range(w):
            try: #Testing if the generator is not empty  
                r=int(next(gen))
                g=int(next(gen))
                b=int(next(gen))
            except StopIteration:
                print("Missing Cell Color")
                return None
            if 0<=r<=255 and 0<=g<=255 and 0<=b<=255:
                l.append((r,g,b))
            else:
                print("Wrong value",(r,g,b))
                return None
        img.append(l)

    return w,h,img
    
    
        
        
def ppm_save(w, h, img, output):
    """takes an output stream output and that saves the PPM image img whose size is w x h.
    """
    with open(output,"w") as out:
        out.write('P3\n'+f'{w} {h} \n'+'255\n')
        for line in img:
            for pixel in line:
                r,g,b=pixel
                out.write(f'{r} {g} {b}\n')

    
def RGB2YCbCr(r, g, b):
    """Takes a pixel’s color in the RGB color space and converts it in the YCbCr color space,
    returning the 3-element tuple (Y, Cb, Cr)
    """   
    Y= min(max(round(0.299*r+0.587*g+0.114*b),0),255)
    Cb=min(max(round(128-0.168736*r-0.331264*g+0.5*b),0),255)
    Cr=min(max(round(128+0.5*r-0.418688*g-0.081312*b),0),255)
    return (Y,Cb,Cr)

def YCbCr2RGB(Y, Cb, Cr):
    """Takes a point in the YCbCr and that converts it in the RGB color space, 
    returning the 3-element tuple (R, G, B).
    """
    
    R=min(max(round(Y+1.402*(Cr-128)),0),255)
    G=min(max(round(Y-0.344136*(Cb-128)-0.714136*(Cr-128)),0),255)
    B=min(max(round(Y+1.772*(Cb-128)),0),255)
    return (R,G,B)

def img_RGB2YCbCr(img):
    """Takes an image in the RGB-color space and returns a 3-element tuple (Y, Cb, Cr)
    where Y (resp. Cb, Cr) is a matrix s.t. Y[i][j] (resp. Cb[i][j], Cr[i][j]) 
    denotes the Y (resp. Cb, Cr) component of img[i][j].
    """
    
    matY=[]
    matCb=[]
    matCr=[]
    for line in img:
        lineY=[]
        lineCb=[]
        lineCr=[]
        for pixel in line:
             Y,Cb,Cr=RGB2YCbCr(pixel[0],pixel[1],pixel[2])
             lineY.append(Y)
             lineCb.append(Cb)
             lineCr.append(Cr)
        matY.append(lineY)
        matCb.append(lineCb)
        matCr.append(lineCr)
    return (matY,matCb,matCr)

def img_YCbCr2RGB(img):
    """Performs the inverse transformation to img_RGB2YCbCr(img)
    """
    matR=[]
    matG=[]
    matB=[]
    for line in img:
        lineR=[]
        lineG=[]
        lineB=[]
        for pixel in line:
             R,G,B=YCbCr2RGB(pixel[0],pixel[1],pixel[2])
             lineR.append(R)
             lineG.append(G)
             lineB.append(B)
        matR.append(lineR)
        matG.append(lineG)
        matB.append(lineB)
    return (matR,matG,matB)
    

def subsampling(w, h, C, a, b):
    """Performs & returns the subsampling of the channel C (of size w x h) in the a:b subsampling mode
    """
    
    M=[] 
    for i in range(0,h,a):
        l = []
        for j in range(0,w,b):
            average=avgmat(C,i,min(i+a,h),j,min(j+b,w))
            l.append(average)
        M.append(l)
    return M
            
     
def avgmat(mat,line_start,line_end,column_start,column_end):
    """Returns the average of a matrix's elements
    """
    
    add=0
    c=0
    for i in range(line_start,line_end):
        for j in range(column_start,column_end):
            add+=mat[i][j]
            c+=1
    return round(add/c)
            
def extrapolate(w, h, C, a, b) :
    """Does the inverse operation of subsampling(), 
    where w & h denotes the size of the channel before the subsampling has been applied
    """
    if  w % b == 0:
        width= w//b
    else:
        width= w//b + 1
        
    if   h % a == 0:
        height= h//a
    else:
        height= h//a + 1
    M=[]
    for i in range(h):
        l=[]
        i1=i//a
        for j in range(w):
            j1=j//b
            l.append(C[i1][j1])
        M.append(l)     
    return M
    
        
def block_splitting(w, h, C) :
    """Takes a channel C and yields all the 8x8 subblocks of the channel,
     line by line, from left to right.
    """
    for i in range(0,h,8):
        for j in range(0,w,8):
            istart=i
            iend=min(i+8,h)
            jstart=j
            jend=min(j+8,w)
            yield block_splitting_aux(C,istart,iend,jstart,jend)
    
def block_splitting_aux(C,linestart,lineend,columnstart,columnend):
    """Auxilary function for block_splitting()
    """
    
    M=[]
    for i in range(8):
        l=[]
        for j in range(8):
            cell=C[min(linestart+i,lineend-1)][min(columnstart+j,columnend-1)]
            l.append(cell)
        M.append(l)
    return M
            
                                  
def DCT(v):
    """Computes and return the DCT-II of the vector v
    """
    
    n=len(v)
    a=0
    l=[]
    for i in range(n):
        if i==0:
            delta=1/math.sqrt(2)
        else:
            delta=1
        for j in range(n):
            a+=v[j]*math.cos((math.pi/n)*(j+0.5)*i)
        l.append((delta*(math.sqrt(2/n))*a))
        a=0
    return l

def IDCT(v):
    """Computes the inverse DCT-II of the vector v
    """
    
    n=len(v)
    a=0
    l=[]
    for i in range(n):
        for j in range(n):
            if j==0:
                delta=1/math.sqrt(2)
            else:
                delta=1
            a+=delta*(math.sqrt(2/n))*v[j]*math.cos((math.pi/n)*(i+0.5)*j)
        l.append(a)
        a=0
    return l

    
                    
def DCT2(m,n,A):
    """computes the 2D DCT-II of the matrix A made of m rows and n columns
    """
    mat=[]
    for row in A:
      mat.append(DCT(row))
    
    mat2=[[0]*n for i in range(m)]
    for j in range(n):
        column=[mat[i][j] for i in range(m)]
        updated_column=DCT(column)
        for i in range(m):
            mat2[i][j]=updated_column[i]
            
    return mat2
    
def C_nij(n,i,j):
    """Gives the i,j th coefficient of c_n
    """
    
    if i==0:
        delta=1/math.sqrt(2)
    else:
        delta=1 
    return delta*(math.sqrt(2/n))*math.cos((math.pi/n)*(j+0.5)*i)
        
def IDCT2(m, n, A):
    """computes the 2D inverse DCT-II of the matrix A made of m rows and n columns
    """
    mat=[]
    for row in A:
      mat.append(IDCT(row))
    
    mat2=[[0]*n for i in range(m)]
    for j in range(n):
        column=[mat[i][j] for i in range(m)]
        updated_column=IDCT(column)
        for i in range(m):
            mat2[i][j]=updated_column[i]
            
    return mat2
    

def redalpha(i):
    """Takes a non-negative integer i and that returns a pair (s, k) s.t.
    s an integer in the set {−1,1},
    k an integer in the range {0..8}, and
    α_i=s*α_k
    """

    i=i%32
    k = i%16
    if k>8:
        if k!=i:
            return (1,16-k)
        else:
            return (-1,16-k)
    else:
        if k!=i:
            return (-1,k)
        else:
            return (1,k)
    
    
def ncoeff8(i, j):
    """takes two integers i & j in the range {0..8} and that returns a pair (s, k) s.t.
    s an integer in the set {−1,1},
    k an integer in the range {0..8}, and
    C¯i,j=s⋅αk.
    """
    
    if i==0:
        return (1,4)
    else:
        return redalpha(i*(2*j+1))


def M8_to_str(M8):
    def for1(s, i):
        return f"{'+' if s >= 0 else '-'}{i:d}"

    return "\n".join(
        " ".join(for1(s, i) for (s, i) in row)
        for row in M8
    )
    
    print(M8_to_str(M8))

#Cmatrix for DCT_Chen
Cmatrix=[[0]*8 for i in range(8)]
for i in range(8):
    for j in range(8):
        Cmatrix[i][j]=C_nij(8,i,j)
          
    
def DCT_Chen_aux(l):
    """computes the terms i of a vector using the formula and returns the vector*Cbar
    """
    #Cmatrix is already computed, so are the (alphas/2) at line 3
    newl=[0]*8
    newl[0]=(alpha_over2[4])*sum(l)
    newl[1]=sum((l[j]-l[7-j])*Cmatrix[1][j] for j in range(4))
    newl[2]=(alpha_over2[2])*(l[0]+l[7]-(l[3]+l[4]))+(alpha_over2[6])*(l[1]+l[6]-(l[2]+l[5]))
    newl[3]=sum((l[j]-l[7-j])*Cmatrix[3][j] for j in range(4))
    newl[4]=(alpha_over2[4])*(l[0]-l[1]-l[2]+l[3]+l[4]-l[5]-l[6]+l[7])
    newl[5]=sum((l[j]-l[7-j])*Cmatrix[5][j] for j in range(4))
    newl[6]=(alpha_over2[2])*(-l[1]+l[2]+l[5]-l[6])+(alpha_over2[6])*(l[0]-l[3]-l[4]+l[7])
    newl[7]=sum((l[j]-l[7-j])*Cmatrix[7][j] for j in range(4))
    return newl

def DCT_Chen(A):
    """takes an 8x8 matrix A of numbers (integers and/or floating point numbers) *
    and returns the 2D DCT-II transform of A
    """
    mat=[]
    for row in A:
        mat.append(DCT_Chen_aux(row))
    
    mat2=[[0]*8 for i in range(8)]
    for j in range(8):
        column=[mat[i][j] for i in range(8)]
        updated_column=DCT_Chen_aux(column)
        for i in range(8):
            mat2[i][j]=updated_column[i]
            
    return mat2
            

  
def IDCT_Chen_aux(l):
    """Precomputes the values we need for IDCT_chen
    """
    #i= V_i and j=alpha(j)
    t=[[0]*8 for i in range(8)]
    
    t[0][4]= l[0]*alpha_over2[4]
    t[4][4]=l[4]*alpha_over2[4]
    
    for i in [2,6]:
        for j in [2,6]:
            t[i][j]=l[i]*alpha_over2[j]
            
    for i in range(1,8,2):
        for j in range(1,8,2):
            t[i][j]=l[i]*alpha_over2[j] 
            
            
    O=[]
    O.append(t[0][4]+t[4][4]+t[2][2]+t[6][6])
    O.append(t[0][4]-t[4][4]+t[2][6]-t[6][2])
    O.append(t[0][4]-t[4][4]-t[2][6]+t[6][2])
    O.append(t[0][4]+t[4][4]-t[2][2]-t[6][6])
    
    T=[]
    T.append(t[1][1]+t[3][3]+t[5][5]+t[7][7])
    T.append(t[1][3]-t[3][7]-t[5][1]-t[7][5])
    T.append(t[1][5]-t[3][1]+t[5][7]+t[7][3])
    T.append(t[1][7]-t[3][5]+t[5][3]-t[7][1])
    L=[0]*8
    for j in range(8):
        if j<=3:
            L[j]=O[j%4]+T[j%4]
        else:
            L[j]=O[3-(j%4)]-T[3-(j%4)]
    return L
    
    
def IDCT_Chen(A):
    """takes an 8x8 matrix A of numbers (integers and/or floating point numbers) 
    and returns the 2D DCT-II inverse transform of A
    """
    
    mat=[]
    for row in A:
        mat.append(IDCT_Chen_aux(row))
    
    mat2=[[0]*8 for i in range(8)]
    for j in range(8):
        column=[mat[i][j] for i in range(8)]
        updated_column=IDCT_Chen_aux(column)
        for i in range(8):
            mat2[i][j]=updated_column[i]
            
    return mat2
        

def quantization(A, Q):
    """takes two 8x8 matrices of numbers (integers and/or floating point numbers) 
    and returns the quantization of A by Q"""
    
    M=[]
    for i in range(8):
        l=[]
        for j in range(8):
            l.append(round(A[i][j]/Q[i][j]))
        M.append(l)
    return M
            
            
def quantizationI(A, Q):
    """takes two 8x8 matrices of numbers (integers and/or floating point numbers) 
    and returns the inverse quantization of A by Q
    """
    
    M=[]
    for i in range(8):
        l=[]
        for j in range(8):
            l.append(A[i][j]*Q[i][j])
        M.append(l)
    return M
    
    
def Qmatrix(isY, phi):
    """takes a boolean isY and a quality factor phi. 
    If isY is True, it returns the standard JPEG quantization matrix for the luminance channel (LQM), 
    lifted by the quality factor phi. 
    If isY is False, it returns the standard JPEG quantization matrix for the chrominance channel (CQM), 
    lifted by the quality factor phi.
    """
    
    LQM = [
  [16, 11, 10, 16,  24,  40,  51,  61],
  [12, 12, 14, 19,  26,  58,  60,  55],
  [14, 13, 16, 24,  40,  57,  69,  56],
  [14, 17, 22, 29,  51,  87,  80,  62],
  [18, 22, 37, 56,  68, 109, 103,  77],
  [24, 35, 55, 64,  81, 104, 113,  92],
  [49, 64, 78, 87, 103, 121, 120, 101],
  [72, 92, 95, 98, 112, 100, 103,  99],
]

    CQM = [
  [17, 18, 24, 47, 99, 99, 99, 99],
  [18, 21, 26, 66, 99, 99, 99, 99],
  [24, 26, 56, 99, 99, 99, 99, 99],
  [47, 66, 99, 99, 99, 99, 99, 99],
  [99, 99, 99, 99, 99, 99, 99, 99],
  [99, 99, 99, 99, 99, 99, 99, 99],
  [99, 99, 99, 99, 99, 99, 99, 99],
  [99, 99, 99, 99, 99, 99, 99, 99],
]
    Q=[]
    if phi>=50:
        S=200-2*phi
    else:
        S=round(5000/phi)
    if isY is True:
        for i in range(8):
            l=[]
            for j in range(8):
                l.append(math.ceil((50+S*LQM[i][j])/100))
            Q.append(l)
        return Q
    else:
        for i in range(8):
            l=[]
            for j in range(8):
                l.append(math.ceil((50+S*CQM[i][j])/100))
            Q.append(l)
        return Q
  
def zigzag(A):
    """ takes a 8x8 row-major matrix and that returns a generator that yields all the values of A,
    following the zig-zag ordering.
    """
    increment=1
    for s in range(15):
        start=max(0,s-7)+min(0,increment)
        end=min(7,s)+max(0,increment)
        if increment<0:
            start,end=end,start
        for j in range(start,end,increment):
            i=s-j
            yield A[i][j]
        increment*=-1
        
            

def rle0(g):
    """takes a generator that yields integers and that returns a generator 
    that yields the pairs obtained from the RLE0 encoding of g.
    """
    
    z=0
    for n in g: #The function in the grader takes as input an iterator (list) and not a generator
        if n==0:
            z+=1
        else:
            yield(z,n)
            z=0
    