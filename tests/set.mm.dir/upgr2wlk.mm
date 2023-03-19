include "cupgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "upgriswlk.mm"
include "anbi1d.mm"
include "wb.mm"
include "iswrdb.mm"
include "oveq2.mm"
include "feq2d.mm"
include "syl5bb.mm"
include "fzo0to2pr.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "2wlklem.mm"
include "syl6bb.mm"
include "3anbi123d.mm"
include "adantl.mm"
include "3anass.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "an32.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "cn0.mm"
include "2nn0.mm"
include "fnfzo0hash.mm"
include "mpan.mm"
include "pm4.71i.mm"
include "bicomi.mm"
include "a1i.mm"
include "3anbi1d.mm"
include "3bitrd.mm"

theorem upgr2wlk
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cE: class E
  let vk: setvar k
  assume upgr2wlk.v: |- V = ( Vtx ` G )
  assume upgr2wlk.i: |- I = ( iEdg ` G )


  assert |- ( G e. UPGraph -> ( ( F ( Walks ` G ) P /\ ( # ` F ) = 2 ) <-> ( F : ( 0 ..^ 2 ) --> dom I /\ P : ( 0 ... 2 ) --> V /\ ( ( I ` ( F ` 0 ) ) = { ( P ` 0 ) , ( P ` 1 ) } /\ ( I ` ( F ` 1 ) ) = { ( P ` 1 ) , ( P ` 2 ) } ) ) ) )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    cc0
    @2
    cfz
    co
    #
    cV
    cP
    wf
    #
    vk
    cv
    #
    cF
    cfv
    cI
    cfv
    @8
    cP
    cfv
    @8
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    #
    vk
    cc0
    @2
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @3
    wa
    #
    cc0
    c2
    cfzo
    co
    #
    @4
    cF
    wf
    #
    @3
    wa
    #
    cc0
    c2
    cfz
    co
    #
    cV
    cP
    wf
    #
    cc0
    cF
    cfv
    cI
    cfv
    cc0
    cP
    cfv
    c1
    cP
    cfv
    #
    cpr
    wceq
    c1
    cF
    cfv
    cI
    cfv
    @19
    c2
    cP
    cfv
    cpr
    wceq
    wa
    #
    w3a
    #
    @15
    @18
    @20
    w3a
    #
    @0
    @1
    @12
    @3
    cP
    vk
    cF
    cG
    cI
    cV
    upgr2wlk.v
    upgr2wlk.i
    upgriswlk
    anbi1d
    @0
    @13
    @15
    @18
    @20
    wa
    #
    wa
    #
    @3
    wa
    #
    @21
    @0
    @3
    @12
    @24
    @0
    @3
    @12
    @24
    wb
    @0
    @3
    wa
    @12
    @22
    @24
    @3
    @12
    @22
    wb
    @0
    @3
    @5
    @15
    @7
    @18
    @11
    @20
    @5
    @10
    @4
    cF
    wf
    @3
    @15
    @4
    cF
    iswrdb
    @3
    @10
    @14
    @4
    cF
    @2
    c2
    cc0
    cfzo
    oveq2
    #
    feq2d
    syl5bb
    @3
    @6
    @17
    cV
    cP
    @2
    c2
    cc0
    cfz
    oveq2
    feq2d
    @3
    @11
    @9
    vk
    cc0
    c1
    cpr
    #
    wral
    @20
    @3
    @9
    vk
    @10
    @27
    @3
    @10
    @14
    @27
    @26
    fzo0to2pr
    syl6eq
    raleqdv
    cP
    vk
    cI
    cF
    2wlklem
    syl6bb
    3anbi123d
    adantl
    @15
    @18
    @20
    3anass
    syl6bb
    ex
    pm5.32rd
    @21
    @16
    @23
    wa
    @25
    @16
    @18
    @20
    3anass
    @15
    @3
    @23
    an32
    bitri
    syl6bbr
    @0
    @16
    @15
    @18
    @20
    @16
    @15
    wb
    @0
    @15
    @16
    @15
    @3
    c2
    cn0
    wcel
    @15
    @3
    2nn0
    @4
    cF
    c2
    fnfzo0hash
    mpan
    pm4.71i
    bicomi
    a1i
    3anbi1d
    3bitrd
end
