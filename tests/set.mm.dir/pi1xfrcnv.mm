include "ccnv.mm"
include "wceq.mm"
include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "pi1xfrcnvlem.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "cphtpc.mm"
include "cfv.mm"
include "cec.mm"
include "cpco.mm"
include "cbs.mm"
include "cuni.mm"
include "wa.mm"
include "fvex.mm"
include "ecexg.mm"
include "mp1i.mm"
include "fliftrel.mm"
include "df-rel.mm"
include "sylibr.mm"
include "dfrel2.mm"
include "sylib.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "cmin.mm"
include "cmpt.mm"
include "cop.mm"
include "crn.mm"
include "cpi1.mm"
include "0elunit.mm"
include "oveq2.mm"
include "1m0e1.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "eqtr4i.mm"
include "1elunit.mm"
include "1m1e0.mm"
include "fveq2i.mm"
include "eqid.mm"
include "cii.mm"
include "ccn.mm"
include "w3a.mm"
include "pcorevcl.mm"
include "syl.mm"
include "simp1d.mm"
include "cbvmptv.mm"
include "ctopon.mm"
include "wf.mm"
include "iitopon.mm"
include "a1i.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "feqmptd.mm"
include "iirev.mm"
include "cc.mm"
include "ax-1cn.mm"
include "cr.mm"
include "unitssre.mm"
include "sseli.mm"
include "recnd.mm"
include "nncan.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "eceq1d.mm"
include "opeq2d.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "cnveqd.mm"
include "unieqd.mm"
include "oveq2d.mm"
include "mpteq12dv.mm"
include "3sstr4d.mm"
include "cnvss.mm"
include "eqsstr3d.mm"
include "eqssd.mm"
include "pi1xfr.mm"
include "eqeltrd.mm"
include "jca.mm"

theorem pi1xfrcnv
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vs: setvar s
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume pi1xfr.p: |- P = ( J pi1 ( F ` 0 ) )
  assume pi1xfr.q: |- Q = ( J pi1 ( F ` 1 ) )
  assume pi1xfr.b: |- B = ( Base ` P )
  assume pi1xfr.g: |- G = ran ( g e. U. B |-> <. [ g ] ( ~=ph ` J ) , [ ( I ( *p ` J ) ( g ( *p ` J ) F ) ) ] ( ~=ph ` J ) >. )
  assume pi1xfr.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1xfr.f: |- ( ph -> F e. ( II Cn J ) )
  assume pi1xfr.i: |- I = ( x e. ( 0 [,] 1 ) |-> ( F ` ( 1 - x ) ) )
  assume pi1xfrcnv.h: |- H = ran ( h e. U. ( Base ` Q ) |-> <. [ h ] ( ~=ph ` J ) , [ ( F ( *p ` J ) ( h ( *p ` J ) I ) ) ] ( ~=ph ` J ) >. )

  disjoint g h
  disjoint g x
  disjoint B g
  disjoint h x
  disjoint B h
  disjoint B x
  disjoint F g
  disjoint F h
  disjoint F x
  disjoint I g
  disjoint I h
  disjoint I x
  disjoint G h
  disjoint g ph
  disjoint h ph
  disjoint ph x
  disjoint J g
  disjoint J h
  disjoint J x
  disjoint P g
  disjoint P h
  disjoint P x
  disjoint Q g
  disjoint Q h
  disjoint Q x
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g s
  disjoint g u
  disjoint g y
  disjoint g z
  disjoint h s
  disjoint h u
  disjoint h y
  disjoint h z
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F s
  disjoint F u
  disjoint F y
  disjoint F z
  disjoint I s
  disjoint I u
  disjoint I y
  disjoint I z
  disjoint A g
  disjoint A s
  disjoint A x
  disjoint G f
  disjoint G y
  disjoint G z
  disjoint H f
  disjoint H s
  disjoint H z
  disjoint f ph
  disjoint ph s
  disjoint ph u
  disjoint ph y
  disjoint ph z
  disjoint J f
  disjoint J s
  disjoint J u
  disjoint J y
  disjoint J z
  disjoint P f
  disjoint P s
  disjoint P y
  disjoint P z
  disjoint Q f
  disjoint Q s
  disjoint Q y
  disjoint Q z
  assert |- ( ph -> ( `' G = H /\ `' G e. ( Q GrpHom P ) ) )

  proof
    wph
    cG
    ccnv
    #
    cH
    wceq
    @0
    cQ
    cP
    cghm
    co
    #
    wcel
    wph
    @0
    cH
    wph
    vx
    cB
    cP
    cQ
    vg
    vh
    cF
    cG
    cH
    cI
    cJ
    cX
    pi1xfr.p
    pi1xfr.q
    pi1xfr.b
    pi1xfr.g
    pi1xfr.j
    pi1xfr.f
    pi1xfr.i
    pi1xfrcnv.h
    pi1xfrcnvlem
    wph
    cH
    cH
    ccnv
    #
    ccnv
    #
    @0
    wph
    cH
    wrel
    #
    @3
    cH
    wceq
    wph
    cH
    cvv
    cvv
    cxp
    wss
    @4
    wph
    vh
    vh
    cv
    #
    cJ
    cphtpc
    cfv
    #
    cec
    #
    cF
    @5
    cI
    cJ
    cpco
    cfv
    #
    co
    #
    @8
    co
    #
    @6
    cec
    #
    cvv
    cvv
    cH
    cQ
    cbs
    cfv
    #
    cuni
    #
    pi1xfrcnv.h
    @6
    cvv
    wcel
    #
    @7
    cvv
    wcel
    wph
    @5
    @13
    wcel
    wa
    #
    cJ
    cphtpc
    fvex
    #
    @5
    cvv
    @6
    ecexg
    mp1i
    @14
    @11
    cvv
    wcel
    @15
    @16
    @10
    cvv
    @6
    ecexg
    mp1i
    fliftrel
    cH
    df-rel
    sylibr
    cH
    dfrel2
    sylib
    wph
    @2
    cG
    wss
    @3
    @0
    wss
    wph
    vh
    @13
    @7
    vz
    cc0
    c1
    cicc
    co
    #
    c1
    vz
    cv
    #
    cmin
    co
    #
    cI
    cfv
    #
    cmpt
    #
    @9
    @8
    co
    #
    @6
    cec
    #
    cop
    #
    cmpt
    #
    crn
    #
    ccnv
    vg
    cP
    cbs
    cfv
    #
    cuni
    #
    vg
    cv
    #
    @6
    cec
    #
    cI
    @29
    @21
    @8
    co
    #
    @8
    co
    #
    @6
    cec
    #
    cop
    #
    cmpt
    #
    crn
    #
    @2
    cG
    wph
    vy
    @12
    cQ
    cP
    vh
    vg
    cI
    @26
    @36
    @21
    cJ
    cX
    cQ
    cJ
    c1
    cF
    cfv
    #
    cpi1
    co
    cJ
    cc0
    cI
    cfv
    #
    cpi1
    co
    pi1xfr.q
    @38
    @37
    cJ
    cpi1
    cc0
    @17
    wcel
    @38
    @37
    wceq
    #
    0elunit
    vx
    cc0
    c1
    vx
    cv
    #
    cmin
    co
    #
    cF
    cfv
    #
    @37
    @17
    cI
    @40
    cc0
    wceq
    #
    @41
    c1
    cF
    @43
    @41
    c1
    cc0
    cmin
    co
    c1
    @40
    cc0
    c1
    cmin
    oveq2
    1m0e1
    syl6eq
    fveq2d
    pi1xfr.i
    c1
    cF
    fvex
    fvmpt
    ax-mp
    oveq2i
    eqtr4i
    #
    cP
    cJ
    cc0
    cF
    cfv
    #
    cpi1
    co
    cJ
    c1
    cI
    cfv
    #
    cpi1
    co
    pi1xfr.p
    @46
    @45
    cJ
    cpi1
    c1
    @17
    wcel
    @46
    @45
    wceq
    #
    1elunit
    vx
    c1
    @42
    @45
    @17
    cI
    @40
    c1
    wceq
    #
    @42
    c1
    c1
    cmin
    co
    #
    cF
    cfv
    @45
    @48
    @41
    @49
    cF
    @40
    c1
    c1
    cmin
    oveq2
    fveq2d
    @49
    cc0
    cF
    1m1e0
    fveq2i
    syl6eq
    pi1xfr.i
    cc0
    cF
    fvex
    fvmpt
    ax-mp
    oveq2i
    eqtr4i
    #
    @12
    eqid
    #
    @26
    eqid
    #
    pi1xfr.j
    wph
    cI
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    @39
    @47
    wph
    cF
    @53
    wcel
    #
    @54
    @39
    @47
    w3a
    pi1xfr.f
    vx
    cF
    cI
    cJ
    pi1xfr.i
    pcorevcl
    syl
    simp1d
    #
    vz
    vy
    @17
    @20
    c1
    vy
    cv
    #
    cmin
    co
    #
    cI
    cfv
    @18
    @57
    wceq
    @19
    @58
    cI
    @18
    @57
    c1
    cmin
    oveq2
    fveq2d
    cbvmptv
    #
    @36
    eqid
    pi1xfrcnvlem
    wph
    cH
    @26
    wph
    cH
    vh
    @13
    @7
    @11
    cop
    #
    cmpt
    #
    crn
    @26
    pi1xfrcnv.h
    wph
    @61
    @25
    wph
    vh
    @13
    @60
    @24
    wph
    @11
    @23
    @7
    wph
    @10
    @22
    @6
    wph
    cF
    @21
    @9
    @8
    wph
    cF
    vz
    @17
    @18
    cF
    cfv
    #
    cmpt
    @21
    wph
    vz
    @17
    cX
    cF
    wph
    cii
    @17
    ctopon
    cfv
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    @55
    @17
    cX
    cF
    wf
    @63
    wph
    iitopon
    a1i
    pi1xfr.j
    pi1xfr.f
    cF
    cii
    cJ
    @17
    cX
    cnf2
    syl3anc
    feqmptd
    vz
    @17
    @20
    @62
    @18
    @17
    wcel
    #
    @20
    c1
    @19
    cmin
    co
    #
    cF
    cfv
    #
    @62
    @64
    @19
    @17
    wcel
    @20
    @66
    wceq
    @18
    iirev
    vx
    @19
    @42
    @66
    @17
    cI
    @40
    @19
    wceq
    @41
    @65
    cF
    @40
    @19
    c1
    cmin
    oveq2
    fveq2d
    pi1xfr.i
    @65
    cF
    fvex
    fvmpt
    syl
    @64
    @65
    @18
    cF
    @64
    c1
    cc
    wcel
    @18
    cc
    wcel
    @65
    @18
    wceq
    ax-1cn
    @64
    @18
    @17
    cr
    @18
    unitssre
    sseli
    recnd
    c1
    @18
    nncan
    sylancr
    fveq2d
    eqtrd
    mpteq2ia
    syl6eqr
    #
    oveq1d
    eceq1d
    opeq2d
    mpteq2dv
    rneqd
    syl5eq
    #
    cnveqd
    wph
    cG
    vg
    cB
    cuni
    #
    @30
    cI
    @29
    cF
    @8
    co
    #
    @8
    co
    #
    @6
    cec
    #
    cop
    #
    cmpt
    #
    crn
    @36
    pi1xfr.g
    wph
    @74
    @35
    wph
    vg
    @69
    @73
    @28
    @34
    wph
    cB
    @27
    cB
    @27
    wceq
    wph
    pi1xfr.b
    a1i
    unieqd
    wph
    @72
    @33
    @30
    wph
    @71
    @32
    @6
    wph
    @70
    @31
    cI
    @8
    wph
    cF
    @21
    @29
    @8
    @67
    oveq2d
    oveq2d
    eceq1d
    opeq2d
    mpteq12dv
    rneqd
    syl5eq
    3sstr4d
    @2
    cG
    cnvss
    syl
    eqsstr3d
    eqssd
    #
    wph
    @0
    @26
    @1
    wph
    @0
    cH
    @26
    @75
    @68
    eqtrd
    wph
    vy
    @12
    cQ
    cP
    vh
    cI
    @26
    @21
    cJ
    cX
    @44
    @50
    @51
    @52
    pi1xfr.j
    @56
    @59
    pi1xfr
    eqeltrd
    jca
end
