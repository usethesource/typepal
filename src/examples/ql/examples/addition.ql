form addition { 
  "Enter number 1:"
    x: integer
  "Enter number 2:"
    y: integer 

  /* The result is computed based on {x} and {y} 
   * using sumation as in {x + y} and not logical
   * conjunction as in {x && y}
   */   


  "The sum is: " sum: integer = x + y 
}