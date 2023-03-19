include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "eluzel2.mm"
include "simp1.mm"
include "wa.mm"
include "eluz1.mm"
include "ibar.mm"
include "bitrd.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "pm5.21nii.mm"

theorem eluz2
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( N e. ( ZZ>= ` M ) <-> ( M e. ZZ /\ N e. ZZ /\ M <_ N ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cM
    cz
    wcel
    #
    @1
    cN
    cz
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    w3a
    #
    cM
    cN
    eluzel2
    @1
    @2
    @3
    simp1
    @1
    @0
    @1
    @2
    @3
    wa
    #
    wa
    #
    @4
    @1
    @0
    @5
    @6
    cM
    cN
    eluz1
    @1
    @5
    ibar
    bitrd
    @1
    @2
    @3
    3anass
    syl6bbr
    pm5.21nii
end
