include "cv.mm"
include "cfv.mm"
include "csuc.mm"
include "c1o.mm"
include "cop.mm"
include "csn.mm"
include "wbr.mm"
include "com.mm"
include "wral.mm"
include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "1n0.mm"
include "df-br.mm"
include "elsni.mm"
include "fvex.mm"
include "opth1.mm"
include "syl.mm"
include "sylbi.mm"
include "tz6.12i.mm"
include "mpsyl.mm"
include "vex.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "breldm.mm"
include "ralimi.mm"
include "dfss3.mm"
include "sylibr.mm"
include "dmex.mm"
include "ssex.mm"
include "wex.mm"
include "crn.mm"
include "wa.mm"
include "wi.mm"
include "snex.mm"
include "wb.mm"
include "fvsn.mm"
include "wfun.mm"
include "funsn.mm"
include "snid.mm"
include "dmsnop.mm"
include "eleqtrri.mm"
include "funbrfvb.mm"
include "mp2an.mm"
include "mpbi.mm"
include "breq12.mm"
include "spc2ev.mm"
include "ax-mp.mm"
include "breq.mm"
include "2exbidv.mm"
include "mpbiri.mm"
include "ssid.mm"
include "rnsnop.mm"
include "3sstr4i.mm"
include "rneq.mm"
include "dmeq.mm"
include "sseq12d.mm"
include "pm5.5.mm"
include "syl2anc.mm"
include "ralbidv.mm"
include "exbidv.mm"
include "bitrd.mm"
include "ax-dc.mm"
include "vtocl.mm"
include "exlimiiv.mm"

theorem dcomex
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vf: setvar f
  let vn: setvar n


  assert |- _om e. _V

  proof
    vn
    cv
    #
    vf
    cv
    #
    cfv
    #
    @0
    csuc
    #
    @1
    cfv
    #
    c1o
    c1o
    cop
    #
    csn
    #
    wbr
    #
    vn
    com
    wral
    #
    com
    cvv
    wcel
    #
    vf
    @8
    com
    @1
    cdm
    #
    wss
    #
    @9
    @8
    @0
    @10
    wcel
    #
    vn
    com
    wral
    @11
    @7
    @12
    vn
    com
    @7
    @0
    c1o
    @1
    wbr
    #
    @12
    c1o
    c0
    wne
    @7
    @2
    c1o
    wceq
    #
    @13
    1n0
    @7
    @2
    @4
    cop
    #
    @6
    wcel
    #
    @14
    @2
    @4
    @6
    df-br
    @16
    @15
    @5
    wceq
    @14
    @15
    @5
    elsni
    @2
    @4
    c1o
    c1o
    @0
    @1
    fvex
    @3
    @1
    fvex
    opth1
    syl
    sylbi
    @0
    c1o
    @1
    tz6.12i
    mpsyl
    @0
    c1o
    @1
    vn
    vex
    c1o
    con0
    1on
    elexi
    #
    breldm
    syl
    ralimi
    vn
    com
    @10
    dfss3
    sylibr
    com
    @10
    @1
    vf
    vex
    dmex
    ssex
    syl
    vs
    cv
    #
    vt
    cv
    #
    vx
    cv
    #
    wbr
    #
    vt
    wex
    vs
    wex
    #
    @20
    crn
    #
    @20
    cdm
    #
    wss
    #
    wa
    #
    @2
    @4
    @20
    wbr
    #
    vn
    com
    wral
    #
    vf
    wex
    #
    wi
    #
    @8
    vf
    wex
    #
    vx
    @6
    @5
    snex
    @20
    @6
    wceq
    #
    @30
    @29
    @31
    @32
    @22
    @25
    @30
    @29
    wb
    @32
    @22
    @18
    @19
    @6
    wbr
    #
    vt
    wex
    vs
    wex
    #
    c1o
    c1o
    @6
    wbr
    #
    @34
    c1o
    @6
    cfv
    c1o
    wceq
    #
    @35
    c1o
    c1o
    @17
    @17
    fvsn
    @6
    wfun
    c1o
    @6
    cdm
    #
    wcel
    @36
    @35
    wb
    c1o
    c1o
    @17
    @17
    funsn
    c1o
    c1o
    csn
    #
    @37
    c1o
    @17
    snid
    c1o
    c1o
    @17
    dmsnop
    #
    eleqtrri
    c1o
    c1o
    @6
    funbrfvb
    mp2an
    mpbi
    @33
    @35
    vs
    vt
    c1o
    c1o
    @17
    @17
    @18
    c1o
    @19
    c1o
    @6
    breq12
    spc2ev
    ax-mp
    @32
    @21
    @33
    vs
    vt
    @18
    @19
    @20
    @6
    breq
    2exbidv
    mpbiri
    @32
    @25
    @6
    crn
    #
    @37
    wss
    @38
    @38
    @40
    @37
    @38
    ssid
    c1o
    c1o
    @17
    rnsnop
    @39
    3sstr4i
    @32
    @23
    @40
    @24
    @37
    @20
    @6
    rneq
    @20
    @6
    dmeq
    sseq12d
    mpbiri
    @26
    @29
    pm5.5
    syl2anc
    @32
    @28
    @8
    vf
    @32
    @27
    @7
    vn
    com
    @2
    @4
    @20
    @6
    breq
    ralbidv
    exbidv
    bitrd
    vx
    vs
    vt
    vf
    vn
    ax-dc
    vtocl
    exlimiiv
end
