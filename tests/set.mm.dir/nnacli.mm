include "com.mm"
include "wcel.mm"
include "coa.mm"
include "co.mm"
include "nnacl.mm"
include "mp2an.mm"

theorem nnacli
  let cA: class A
  let cB: class B
  assume nncli.1: |- A e. _om
  assume nncli.2: |- B e. _om


  assert |- ( A +o B ) e. _om

  proof
    cA
    com
    wcel
    cB
    com
    wcel
    cA
    cB
    coa
    co
    com
    wcel
    nncli.1
    nncli.2
    cA
    cB
    nnacl
    mp2an
end
