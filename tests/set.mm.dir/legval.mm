include "cleg.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "copab.mm"
include "cstrkg.mm"
include "cvv.mm"
include "elex.mm"
include "citv.mm"
include "wsbc.mm"
include "cds.mm"
include "cbs.mm"
include "w3a.mm"
include "simp1.mm"
include "eqcomd.mm"
include "simp2.mm"
include "oveqd.mm"
include "eqeq2d.mm"
include "simp3.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"
include "sbcie3s.mm"
include "opabbidv.mm"
include "df-leg.mm"
include "wtru.mm"
include "cxp.mm"
include "cima.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "fvex.mm"
include "eqeltri.mm"
include "imaex.mm"
include "p0ex.mm"
include "unex.mm"
include "a1i.mm"
include "simprr.mm"
include "ovima0.mm"
include "ad5ant14.mm"
include "eqeltrd.mm"
include "simpllr.mm"
include "simpld.mm"
include "ad3antrrr.mm"
include "jca.mm"
include "eleq1.mm"
include "oveq2.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "r19.29a.mm"
include "ex.mm"
include "rexlimivv.mm"
include "adantl.mm"
include "simprd.mm"
include "opabex2.mm"
include "trud.mm"
include "fvmpt.mm"
include "3syl.mm"
include "syl5eq.mm"

theorem legval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let ve: setvar e
  let vf: setvar f
  let cG: class G
  let cI: class I
  let c.le: class .<_
  let c.mi: class .-
  let vd: setvar d
  let vg: setvar g
  let vi: setvar i
  let vp: setvar p
  assume legval.p: |- P = ( Base ` G )
  assume legval.d: |- .- = ( dist ` G )
  assume legval.i: |- I = ( Itv ` G )
  assume legval.l: |- .<_ = ( leG ` G )
  assume legval.g: |- ( ph -> G e. TarskiG )

  disjoint e f
  disjoint G e
  disjoint G f
  disjoint x y
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint P e
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint P f
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint .- e
  disjoint .- f
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d i
  disjoint d p
  disjoint G d
  disjoint e g
  disjoint e i
  disjoint e p
  disjoint f g
  disjoint f i
  disjoint f p
  disjoint g i
  disjoint g p
  disjoint G g
  disjoint i p
  disjoint G i
  disjoint G p
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint I d
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint I g
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint I i
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint I p
  disjoint P d
  disjoint P g
  disjoint P i
  disjoint P p
  disjoint .- d
  disjoint .- g
  disjoint .- i
  disjoint .- p
  assert |- ( ph -> .<_ = { <. e , f >. | E. x e. P E. y e. P ( f = ( x .- y ) /\ E. z e. P ( z e. ( x I y ) /\ e = ( x .- z ) ) ) } )

  proof
    wph
    c.le
    cG
    cleg
    cfv
    #
    vf
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    c.mi
    co
    #
    wceq
    #
    vz
    cv
    #
    @2
    @3
    cI
    co
    #
    wcel
    #
    ve
    cv
    #
    @2
    @6
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vz
    cP
    wrex
    #
    wa
    #
    vy
    cP
    wrex
    #
    vx
    cP
    wrex
    #
    ve
    vf
    copab
    #
    legval.l
    wph
    cG
    cstrkg
    wcel
    cG
    cvv
    wcel
    @0
    @17
    wceq
    legval.g
    cG
    cstrkg
    elex
    vg
    cG
    @1
    @2
    @3
    vd
    cv
    #
    co
    #
    wceq
    #
    @6
    @2
    @3
    vi
    cv
    #
    co
    #
    wcel
    #
    @9
    @2
    @6
    @18
    co
    #
    wceq
    #
    wa
    #
    vz
    vp
    cv
    #
    wrex
    #
    wa
    #
    vy
    @27
    wrex
    #
    vx
    @27
    wrex
    #
    vi
    vg
    cv
    #
    citv
    cfv
    wsbc
    vd
    @32
    cds
    cfv
    wsbc
    vp
    @32
    cbs
    cfv
    wsbc
    #
    ve
    vf
    copab
    @17
    cvv
    cleg
    @32
    cG
    wceq
    @33
    @16
    ve
    vf
    @16
    @31
    vg
    cP
    c.mi
    cI
    cbs
    cds
    citv
    cG
    vp
    vd
    vi
    legval.p
    legval.d
    legval.i
    @27
    cP
    wceq
    #
    @18
    c.mi
    wceq
    #
    @21
    cI
    wceq
    #
    w3a
    #
    @15
    @30
    vx
    cP
    @27
    @37
    @27
    cP
    @34
    @35
    @36
    simp1
    eqcomd
    #
    @37
    @14
    @29
    vy
    cP
    @27
    @38
    @37
    @5
    @20
    @13
    @28
    @37
    @4
    @19
    @1
    @37
    c.mi
    @18
    @2
    @3
    @37
    @18
    c.mi
    @34
    @35
    @36
    simp2
    eqcomd
    #
    oveqd
    eqeq2d
    @37
    @12
    @26
    vz
    cP
    @27
    @38
    @37
    @8
    @23
    @11
    @25
    @37
    @7
    @22
    @6
    @37
    cI
    @21
    @2
    @3
    @37
    @21
    cI
    @34
    @35
    @36
    simp3
    eqcomd
    oveqd
    eleq2d
    @37
    @10
    @24
    @9
    @37
    c.mi
    @18
    @2
    @6
    @39
    oveqd
    eqeq2d
    anbi12d
    rexeqbidv
    anbi12d
    rexeqbidv
    rexeqbidv
    sbcie3s
    opabbidv
    vx
    vy
    vz
    ve
    vf
    vg
    vi
    vp
    vd
    df-leg
    @17
    cvv
    wcel
    wtru
    @16
    ve
    vf
    c.mi
    cP
    cP
    cxp
    #
    cima
    #
    c0
    csn
    #
    cun
    #
    @43
    cvv
    cvv
    @43
    cvv
    wcel
    wtru
    @41
    @42
    c.mi
    @40
    c.mi
    cG
    cds
    cfv
    cvv
    legval.d
    cG
    cds
    fvex
    eqeltri
    imaex
    p0ex
    unex
    a1i
    #
    @44
    wtru
    @16
    wa
    #
    @9
    @43
    wcel
    #
    @1
    @43
    wcel
    #
    @16
    @46
    @47
    wa
    #
    wtru
    @14
    @48
    vx
    vy
    cP
    cP
    @2
    cP
    wcel
    #
    @3
    cP
    wcel
    #
    wa
    #
    @14
    @48
    @51
    @14
    wa
    #
    @18
    @7
    wcel
    #
    @9
    @2
    @18
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @48
    vd
    cP
    @52
    @18
    cP
    wcel
    #
    wa
    #
    @56
    wa
    #
    @46
    @47
    @59
    @9
    @54
    @43
    @58
    @53
    @55
    simprr
    @49
    @57
    @54
    @43
    wcel
    @50
    @14
    @56
    cP
    cP
    c.mi
    @2
    @18
    ovima0
    ad5ant14
    eqeltrd
    @59
    @1
    @4
    @43
    @59
    @5
    @13
    @51
    @14
    @57
    @56
    simpllr
    simpld
    @51
    @4
    @43
    wcel
    @14
    @57
    @56
    cP
    cP
    c.mi
    @2
    @3
    ovima0
    ad3antrrr
    eqeltrd
    jca
    @52
    @13
    @56
    vd
    cP
    wrex
    @51
    @5
    @13
    simprr
    @12
    @56
    vz
    vd
    cP
    @6
    @18
    wceq
    #
    @8
    @53
    @11
    @55
    @6
    @18
    @7
    eleq1
    @60
    @10
    @54
    @9
    @6
    @18
    @2
    c.mi
    oveq2
    eqeq2d
    anbi12d
    cbvrexv
    sylib
    r19.29a
    ex
    rexlimivv
    adantl
    #
    simpld
    @45
    @46
    @47
    @61
    simprd
    opabex2
    trud
    fvmpt
    3syl
    syl5eq
end
