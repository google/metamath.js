include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cle.mm"
include "msqge0i.mm"
include "recni.mm"
include "sqvali.mm"
include "breqtrri.mm"

theorem sqge0i
  let cA: class A
  assume resqcl.1: |- A e. RR


  assert |- 0 <_ ( A ^ 2 )

  proof
    cc0
    cA
    cA
    cmul
    co
    cA
    c2
    cexp
    co
    cle
    cA
    resqcl.1
    msqge0i
    cA
    cA
    resqcl.1
    recni
    sqvali
    breqtrri
end
