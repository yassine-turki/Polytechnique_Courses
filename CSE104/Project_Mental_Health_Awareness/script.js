"use strict";



// Title 

const title = document.getElementsByClassName('title')[0];
let clickCount = 0
const brains = []; // Set of circles and their y-coordinates
title.addEventListener("click", createBrain)
title.addEventListener("mouseenter", () => {
	title.innerHTML = "Click for Brains!"
})
title.addEventListener("mouseleave", () => {
	title.innerHTML = "Mental Health"
})
const body = document.querySelector("body");



requestAnimationFrame(animationLoop);



function createBrain() {

  // Create a new Brain where the user clicks
  const x0 = Math.random() * body.clientWidth;
  const y0 = 50
  const brainElement = document.createElement("div");
  brainElement.classList.add('brain');
  brainElement.style = `top:${y0}px; left:${x0}px;`;

  body.appendChild(brainElement);

  // Store this brain  and its y coordinate in an array
  brains.push( { element: brainElement, y: y0 } );
}


// Animation loop
function animationLoop(currentTime) {

  // Translate all brains in y direction
  for (let k=0; k<brains.length; k++) {
    const e = brains[k];
    e.y = e.y + 3;
    e.element.style.top = `${e.y}px`;
  }

  // Remove useless brains
  for(let k=0; k<brains.length; k++) {
    const e = brains[k];
    if( e.y>window.innerHeight ) 
    {
      body.removeChild(e.element);
      brains.splice(k,1);	
    }
  }


  requestAnimationFrame(animationLoop);
}


//Quiz

const q_n = 9;

let score=0;

//Questions

const Questions = [{
  id: 0,
  q: "Mental health is defined as:",
  a: [{ text: "A constant feeling of contentment", isCorrect: false },
    { text: "Striking a balance in all aspects of your life - social, physical, spiritual, economic, mental", isCorrect: true },
    { text: "Achieving a period of 12-18 months without a psychotic episode", isCorrect: false },
    { text: "Not thinking about studies", isCorrect: false }
  ]

},{
  id: 1,
  q: "Suicide is the ________ leading cause of death among people ages 15-34 in the United States.",
  a: [{ text: "24th", isCorrect: false },
    { text: "10th", isCorrect: false },
    { text: "40th", isCorrect: false },
    { text: "2nd", isCorrect: true }
  ]

},
{
  id: 2,
  q: "How many people face mental health issues in France?",
  a: [{ text: "500k", isCorrect: false},
    { text: "3M", isCorrect: false },
    { text: "6M", isCorrect: false },
    { text: "12M", isCorrect: true }
  ]

},
{
  id: 3,
  q: " Are there anyways to help curing mental health problems?",
  a: [{ text: "Talking to someone (family,friends, therapists)", isCorrect: true },
    { text: "Denying your problems", isCorrect: false },
    { text: "Isolate yourself from everyone", isCorrect: false },
    { text: "Wait for things to happen", isCorrect: false }
  ]
},
{
  id: 4,
  q: " What is the average delay between the appearance of mental illness symptoms and treatment ?",
  a: [{ text: "2 days", isCorrect: false },
    { text: "1 month", isCorrect: false },
    { text: "1 year", isCorrect: false },
    { text: "11 years", isCorrect: true }
  ]
},
{
  id: 5,
  q: " If you know someone with poor mental health, you can help by:",
  a: [{ text: "Reaching out and letting them know help is available", isCorrect: false },
    { text: "Helping them acess to mental health services", isCorrect: false },
    { text: "Learning and sharing facts about mental health", isCorrect: false },
    { text: "All of the above", isCorrect: true }
  ]
},
{
  id: 6,
  q: " Mental illness is caused by:",
  a: [{ text: "Personal weakness", isCorrect: false },
    { text: "Lack of willpower", isCorrect: false },
    { text: "A number of factors including biological factors, stressful or traumatic life events and long lasting health conditions such as heart disease or cancer", isCorrect: true },
    { text: "Timid personality", isCorrect: false }
  ]
},
{
  id: 7,
  q: " How many people have depression?",
  a: [{ text: "Less than 100 million", isCorrect: false },
    { text: "At least 100 million but less than 200 million", isCorrect: false },
    { text: "Between 200 million and 300 million", isCorrect: true },
    { text: "More than 300 million", isCorrect: false }
  ]
},
{
  id: 8,
  q: " What are some common symptoms of depression?",
  a: [{ text: "Fatigue or sluggishness", isCorrect: false },
    { text: "Irritability", isCorrect: false },
    { text: "Physical pain, such as headaches or upset stomach", isCorrect: false },
    { text: "All of the Above", isCorrect: true }
  ]
},
{
  id: 9,
  q: " ",
  a: [{ text: "", isCorrect: false },
    { text: "", isCorrect: false },
    { text: "", isCorrect: false },
    { text: "", isCorrect: false }
  ]
}

]

let start = true;

let selected = "none";

var id = 0;


let op1 = document.getElementById('op1');
let op2 = document.getElementById('op2');
let op3 = document.getElementById('op3');
let op4 = document.getElementById('op4');

const evaluate = document.getElementsByClassName("evaluate");
var result = document.getElementsByClassName("result");

const question = document.getElementById("question");

//True or False and color

function handler(){
if (selected == "true") {
		result[0].innerHTML = "True";
		result[0].style.color = "green";
		evaluate[0].style.backgroundColor="green"
	  } else {
		result[0].innerHTML = "False";
		result[0].style.color = "red";
		evaluate[0].style.backgroundColor="red"
	  }	
}

evaluate[0].addEventListener("click", handler)

function iterate(id) {

	result[0].innerText = "";


	question.innerText = Questions[id].q;


	op1.innerText = Questions[id].a[0].text;
	op2.innerText = Questions[id].a[1].text;
	op3.innerText = Questions[id].a[2].text;
	op4.innerText = Questions[id].a[3].text;


	op1.value = Questions[id].a[0].isCorrect;
	op2.value = Questions[id].a[1].isCorrect;
	op3.value = Questions[id].a[2].isCorrect;
	op4.value = Questions[id].a[3].isCorrect;

  //Color when clicking and checking if it is the correct answer

	op1.addEventListener("click", () => {
	  op1.style.backgroundColor = "lightgoldenrodyellow";
	  op2.style.backgroundColor = "#bfbc2d";
	  op3.style.backgroundColor = "#bfbc2d";
	  op4.style.backgroundColor = "#bfbc2d";
	  selected = op1.value;
	})


	op2.addEventListener("click", () => {
	  op1.style.backgroundColor = "#bfbc2d";
	  op2.style.backgroundColor = "lightgoldenrodyellow";
	  op3.style.backgroundColor = "#bfbc2d";
	  op4.style.backgroundColor = "#bfbc2d";
	  selected = op2.value;
	})


	op3.addEventListener("click", () => {
	  op1.style.backgroundColor = "#bfbc2d";
	  op2.style.backgroundColor = "#bfbc2d";
	  op3.style.backgroundColor = "lightgoldenrodyellow";
	  op4.style.backgroundColor = "#bfbc2d";
	  selected = op3.value;
	})


	op4.addEventListener("click", () => {
	  op1.style.backgroundColor = "#bfbc2d";
	  op2.style.backgroundColor = "#bfbc2d";
	  op3.style.backgroundColor = "#bfbc2d";
	  op4.style.backgroundColor = "lightgoldenrodyellow";
	  selected = op4.value;
	})

	
}

if (start) {
	iterate("0");
}

const next = document.getElementsByClassName('next')[0];

next.addEventListener("click", () => {
	
	
	//Add points

	start = false;
	if (id < q_n) {
	  if (selected ==="none") return;
	  id++;
	  iterate(id);
	  if (selected==="true") score++;
	  op1.style.removeProperty("background-color");
	  op2.style.removeProperty("background-color");
	  op3.style.removeProperty("background-color");
	  op4.style.removeProperty("background-color");
	  selected="none";
	}
	if(id === q_n) {
		question.innerText = "You scored " + score + " points!";
		op1.innerText = "The";
	op2.innerText = "game";
	op3.innerText = "is";
	op4.innerText = "over!";
	  next.style.backgroundColor="grey";
	  next.style.disabled = true;
	  next.style.backgroundColor="grey";
	  evaluate[0].style.backgroundColor="grey";
	  evaluate[0].removeEventListener("click", handler);
	}
	

})

