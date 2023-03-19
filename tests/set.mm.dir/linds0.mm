include "wcel.mm"
include "c0.mm"
include "clininds.mm"
include "wbr.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "csca.mm"
include "c0g.mm"
include "cfsupp.mm"
include "clinc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wi.mm"
include "cmap.mm"
include "csn.mm"
include "ral0.mm"
include "2a1i.mm"
include "cvv.mm"
include "wb.mm"
include "0ex.mm"
include "breq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "fveq1.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "ralsng.mm"
include "mp1i.mm"
include "mpbird.mm"
include "c1o.mm"
include "fvex.mm"
include "map0e.mm"
include "df1o2.mm"
include "syl6eq.mm"
include "raleqdv.mm"
include "0elpw.mm"
include "jctil.mm"
include "eqid.mm"
include "islininds.mm"
include "mpan.mm"

theorem linds0
  let cM: class M
  let cV: class V
  let vf: setvar f
  let vx: setvar x
  let vk: setvar k


  assert |- ( M e. V -> (/) linIndS M )

  proof
    cM
    cV
    wcel
    #
    c0
    cM
    clininds
    wbr
    #
    c0
    cM
    cbs
    cfv
    #
    cpw
    wcel
    #
    vf
    cv
    #
    cM
    csca
    cfv
    #
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @4
    c0
    cM
    clinc
    cfv
    #
    co
    #
    cM
    c0g
    cfv
    #
    wceq
    #
    wa
    #
    vx
    cv
    #
    @4
    cfv
    #
    @6
    wceq
    #
    vx
    c0
    wral
    #
    wi
    #
    vf
    @5
    cbs
    cfv
    #
    c0
    cmap
    co
    #
    wral
    #
    wa
    #
    @0
    @20
    @3
    @0
    @20
    @17
    vf
    c0
    csn
    #
    wral
    #
    @0
    @23
    c0
    @6
    cfsupp
    wbr
    #
    c0
    c0
    @8
    co
    #
    @10
    wceq
    #
    wa
    #
    @13
    c0
    cfv
    #
    @6
    wceq
    #
    vx
    c0
    wral
    #
    wi
    #
    @30
    @0
    @27
    @29
    vx
    ral0
    2a1i
    c0
    cvv
    wcel
    #
    @23
    @31
    wb
    @0
    0ex
    @17
    @31
    vf
    c0
    cvv
    @4
    c0
    wceq
    #
    @12
    @27
    @16
    @30
    @33
    @7
    @24
    @11
    @26
    @4
    c0
    @6
    cfsupp
    breq1
    @33
    @9
    @25
    @10
    @4
    c0
    c0
    @8
    oveq1
    eqeq1d
    anbi12d
    @33
    @15
    @29
    vx
    c0
    @33
    @14
    @28
    @6
    @13
    @4
    c0
    fveq1
    eqeq1d
    ralbidv
    imbi12d
    ralsng
    mp1i
    mpbird
    @0
    @17
    vf
    @19
    @22
    @0
    @19
    c1o
    @22
    @18
    cvv
    wcel
    @19
    c1o
    wceq
    @0
    @5
    cbs
    fvex
    @18
    cvv
    map0e
    mp1i
    df1o2
    syl6eq
    raleqdv
    mpbird
    @2
    0elpw
    jctil
    @32
    @0
    @1
    @21
    wb
    0ex
    vx
    @2
    @5
    c0
    vf
    @18
    cM
    cvv
    cV
    @6
    @10
    @2
    eqid
    @10
    eqid
    @5
    eqid
    @18
    eqid
    @6
    eqid
    islininds
    mpan
    mpbird
end
