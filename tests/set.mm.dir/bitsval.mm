include "cbits.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cn0.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "w3a.mm"
include "cdm.mm"
include "cv.mm"
include "crab.mm"
include "df-bits.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "bitsfval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "notbid.mm"
include "elrab.mm"
include "syl6bb.mm"
include "biadan2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem bitsval
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vm: setvar m


  assert |- ( M e. ( bits ` N ) <-> ( N e. ZZ /\ M e. NN0 /\ -. 2 || ( |_ ` ( N / ( 2 ^ M ) ) ) ) )

  proof
    cM
    cN
    cbits
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cn0
    wcel
    #
    c2
    cN
    c2
    cM
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    wa
    #
    wa
    @2
    @3
    @8
    w3a
    @1
    @2
    @9
    @1
    cbits
    cdm
    cz
    cN
    vn
    cz
    c2
    vn
    cv
    c2
    vm
    cv
    #
    cexp
    co
    #
    cdiv
    co
    cfl
    cfv
    cdvds
    wbr
    wn
    vm
    cn0
    crab
    cbits
    vm
    vn
    df-bits
    dmmptss
    cM
    cN
    cbits
    elfvdm
    sseldi
    @2
    @1
    cM
    c2
    cN
    @11
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    vm
    cn0
    crab
    #
    wcel
    @9
    @2
    @0
    @16
    cM
    vm
    cN
    bitsfval
    eleq2d
    @15
    @8
    vm
    cM
    cn0
    @10
    cM
    wceq
    #
    @14
    @7
    @17
    @13
    @6
    c2
    cdvds
    @17
    @12
    @5
    cfl
    @17
    @11
    @4
    cN
    cdiv
    @10
    cM
    c2
    cexp
    oveq2
    oveq2d
    fveq2d
    breq2d
    notbid
    elrab
    syl6bb
    biadan2
    @2
    @3
    @8
    3anass
    bitr4i
end
