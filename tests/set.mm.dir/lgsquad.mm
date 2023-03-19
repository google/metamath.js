include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cfz.mm"
include "wa.mm"
include "cmul.mm"
include "clt.mm"
include "wbr.mm"
include "copab.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "eqid.mm"
include "weq.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "oveq1.mm"
include "breqan12rd.mm"
include "anbi12d.mm"
include "cbvopabv.mm"
include "lgsquadlem3.mm"

theorem lgsquad
  let cP: class P
  let cQ: class Q
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( P e. ( Prime \ { 2 } ) /\ Q e. ( Prime \ { 2 } ) /\ P =/= Q ) -> ( ( P /L Q ) x. ( Q /L P ) ) = ( -u 1 ^ ( ( ( P - 1 ) / 2 ) x. ( ( Q - 1 ) / 2 ) ) ) )

  proof
    cP
    cprime
    c2
    csn
    cdif
    #
    wcel
    #
    cQ
    @0
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    vz
    vw
    cP
    cQ
    vx
    cv
    #
    c1
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cfz
    co
    #
    wcel
    #
    vy
    cv
    #
    c1
    cQ
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    @8
    cP
    cmul
    co
    #
    @4
    cQ
    cmul
    co
    #
    clt
    wbr
    #
    wa
    #
    vx
    vy
    copab
    @5
    @9
    @1
    @2
    @3
    simp1
    @1
    @2
    @3
    simp2
    @1
    @2
    @3
    simp3
    @5
    eqid
    @9
    eqid
    @16
    vz
    cv
    #
    @6
    wcel
    #
    vw
    cv
    #
    @10
    wcel
    #
    wa
    #
    @19
    cP
    cmul
    co
    #
    @17
    cQ
    cmul
    co
    #
    clt
    wbr
    #
    wa
    vx
    vy
    vz
    vw
    vx
    vz
    weq
    #
    vy
    vw
    weq
    #
    wa
    @12
    @21
    @15
    @24
    @25
    @7
    @18
    @26
    @11
    @20
    @4
    @17
    @6
    eleq1
    @8
    @19
    @10
    eleq1
    bi2anan9
    @26
    @25
    @13
    @22
    @14
    @23
    clt
    @8
    @19
    cP
    cmul
    oveq1
    @4
    @17
    cQ
    cmul
    oveq1
    breqan12rd
    anbi12d
    cbvopabv
    lgsquadlem3
end
