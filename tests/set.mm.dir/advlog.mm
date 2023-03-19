include "cr.mm"
include "crp.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "cmpt.mm"
include "cdv.mm"
include "wceq.mm"
include "wtru.mm"
include "cdiv.mm"
include "caddc.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "wa.mm"
include "rpre.mm"
include "adantl.mm"
include "recnd.mm"
include "1cnd.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "recn.mm"
include "1red.mm"
include "dvmptid.mm"
include "wss.mm"
include "rpssre.mm"
include "eqid.mm"
include "tgioo2.mm"
include "cc0.mm"
include "cpnf.mm"
include "ioorp.mm"
include "iooretop.mm"
include "eqeltrri.mm"
include "dvmptres.mm"
include "relogcl.mm"
include "peano2rem.mm"
include "syl.mm"
include "rpreccl.mm"
include "rpcnd.mm"
include "cres.mm"
include "dvrelog.mm"
include "wf1o.mm"
include "wf.mm"
include "relogf1o.mm"
include "f1of.mm"
include "mp1i.mm"
include "feqmptd.mm"
include "fvres.mm"
include "mpteq2ia.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "syl5reqr.mm"
include "0cnd.mm"
include "dvmptc.mm"
include "dvmptsub.mm"
include "subid1d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "dvmptmul.mm"
include "mulid2d.mm"
include "wne.mm"
include "rpne0.mm"
include "recid2d.mm"
include "oveq12d.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "trud.mm"

theorem advlog
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let vy: setvar y
  let cA: class A
  let cN: class N


  assert |- ( RR _D ( x e. RR+ |-> ( x x. ( ( log ` x ) - 1 ) ) ) ) = ( x e. RR+ |-> ( log ` x ) )

  proof
    cr
    vx
    crp
    vx
    cv
    #
    @0
    clog
    cfv
    #
    c1
    cmin
    co
    #
    cmul
    co
    cmpt
    cdv
    co
    #
    vx
    crp
    @1
    cmpt
    #
    wceq
    wtru
    @3
    vx
    crp
    c1
    @2
    cmul
    co
    #
    c1
    @0
    cdiv
    co
    #
    @0
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    @4
    wtru
    vx
    @0
    c1
    @2
    @6
    cr
    cc
    cc
    crp
    cr
    cr
    cc
    cpr
    wcel
    wtru
    reelprrecn
    a1i
    #
    wtru
    @0
    crp
    wcel
    #
    wa
    #
    @0
    @10
    @0
    cr
    wcel
    #
    wtru
    @0
    rpre
    adantl
    recnd
    #
    @11
    1cnd
    #
    wtru
    vx
    @0
    c1
    cr
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    cr
    cr
    crp
    @9
    @12
    @0
    cc
    wcel
    wtru
    @0
    recn
    adantl
    wtru
    @12
    wa
    #
    1red
    wtru
    vx
    cr
    @9
    dvmptid
    crp
    cr
    wss
    wtru
    rpssre
    a1i
    #
    @16
    @16
    eqid
    #
    tgioo2
    #
    @19
    crp
    @15
    wcel
    wtru
    cc0
    cpnf
    cioo
    co
    crp
    @15
    ioorp
    cc0
    cpnf
    iooretop
    eqeltrri
    a1i
    #
    dvmptres
    @11
    @2
    @11
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    @10
    @22
    wtru
    @0
    relogcl
    adantl
    #
    @1
    peano2rem
    syl
    recnd
    #
    @11
    @6
    @10
    @6
    crp
    wcel
    wtru
    @0
    rpreccl
    adantl
    rpcnd
    #
    wtru
    cr
    vx
    crp
    @2
    cmpt
    cdv
    co
    vx
    crp
    @6
    cc0
    cmin
    co
    #
    cmpt
    vx
    crp
    @6
    cmpt
    #
    wtru
    vx
    @1
    @6
    c1
    cc0
    cr
    cc
    cc
    crp
    @9
    @11
    @1
    @23
    recnd
    #
    @25
    wtru
    @27
    cr
    clog
    crp
    cres
    #
    cdv
    co
    cr
    @4
    cdv
    co
    vx
    dvrelog
    wtru
    @29
    @4
    cr
    cdv
    wtru
    @29
    vx
    crp
    @0
    @29
    cfv
    #
    cmpt
    @4
    wtru
    vx
    crp
    cr
    @29
    crp
    cr
    @29
    wf1o
    crp
    cr
    @29
    wf
    wtru
    relogf1o
    crp
    cr
    @29
    f1of
    mp1i
    feqmptd
    vx
    crp
    @30
    @1
    @0
    crp
    clog
    fvres
    mpteq2ia
    syl6eq
    oveq2d
    syl5reqr
    @14
    @11
    0cnd
    wtru
    vx
    c1
    cc0
    cr
    @15
    @16
    cc
    cr
    crp
    @9
    @17
    1cnd
    @17
    0cnd
    wtru
    vx
    c1
    cr
    @9
    wtru
    1cnd
    dvmptc
    @18
    @20
    @19
    @21
    dvmptres
    dvmptsub
    wtru
    vx
    crp
    @26
    @6
    @11
    @6
    @25
    subid1d
    mpteq2dva
    eqtrd
    dvmptmul
    wtru
    vx
    crp
    @8
    @1
    @11
    @8
    @2
    c1
    caddc
    co
    #
    @1
    @11
    @5
    @2
    @7
    c1
    caddc
    @11
    @2
    @24
    mulid2d
    @11
    @0
    @13
    @10
    @0
    cc0
    wne
    wtru
    @0
    rpne0
    adantl
    recid2d
    oveq12d
    @11
    @1
    cc
    wcel
    c1
    cc
    wcel
    @31
    @1
    wceq
    @28
    ax-1cn
    @1
    c1
    npcan
    sylancl
    eqtrd
    mpteq2dva
    eqtrd
    trud
end
