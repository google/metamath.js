include "fvresi.mm"

theorem tendospid
  let cT: class T
  let cF: class F


  assert |- ( F e. T -> ( ( _I |` T ) ` F ) = F )

  proof
    cT
    cF
    fvresi
end
