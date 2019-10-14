form taxOfficeExample { 
  "Did you sell a house in 2010?"
    hasSoldHouse: boolean [false]
  "Did you buy a house in 2010?"
    hasBoughtHouse: boolean [true] 
  "Did you enter a loan?"
    hasMaintLoan: boolean
 
  if (hasSoldHouse) {
    "What was the selling price?"
      sellingPrice: money [809.0] 
    "Private debts for the sold house:"
      privateDebt: money [100.0] 
    "Value residue:"  
      valueResidue: money = (sellingPrice - privateDebt) [709.0]
      
  }
}