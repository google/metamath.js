include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "eluzfz2.mm"
include "elfzuz.mm"
include "impbii.mm"

theorem eluzfz2b
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) <-> N e. ( M ... N ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    cN
    cM
    cN
    cfz
    co
    wcel
    cM
    cN
    eluzfz2
    cN
    cM
    cN
    elfzuz
    impbii
end
