include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "cgrp.mm"
include "cvv.mm"
include "wa.mm"
include "cxp.mm"
include "wf.mm"
include "c0g.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cplusg.mm"
include "wral.mm"
include "cga.mm"
include "ghmgrp1.mm"
include "c0.mm"
include "wne.mm"
include "ghmgrp2.mm"
include "grpn0.mm"
include "wn.mm"
include "csymg.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "necon1ai.mm"
include "3syl.mm"
include "jca.mm"
include "wf1o.mm"
include "cbs.mm"
include "eqid.mm"
include "ghmf.mm"
include "ffvelrnda.mm"
include "wb.mm"
include "adantr.mm"
include "elsymgbas.mm"
include "syl.mm"
include "mpbid.mm"
include "f1of.mm"
include "ralrimiva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "cid.mm"
include "cres.mm"
include "grpidcl.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "fvex.mm"
include "ovmpt2.mm"
include "sylan.mm"
include "ghmid.mm"
include "symgid.mm"
include "eqtr4d.mm"
include "fvresi.mm"
include "adantl.mm"
include "3eqtrd.mm"
include "ccom.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "ffvelrnd.mm"
include "simplr.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "simpll.mm"
include "simprl.mm"
include "ghmlin.mm"
include "syl3anc.mm"
include "symgov.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "grpcl.mm"
include "oveq2d.mm"
include "ralrimivva.mm"
include "isga.mm"
include "sylanbrc.mm"

theorem lactghmga
  let vx: setvar x
  let vy: setvar y
  let c.po: class .(+)
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  assume lactghmga.x: |- X = ( Base ` G )
  assume lactghmga.h: |- H = ( SymGrp ` Y )
  assume lactghmga.f: |- .(+) = ( x e. X , y e. Y |-> ( ( F ` x ) ` y ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G u
  disjoint G v
  disjoint G z
  disjoint H u
  disjoint H v
  disjoint H z
  disjoint .(+) u
  disjoint .(+) v
  disjoint .(+) z
  disjoint X u
  disjoint X v
  disjoint Y u
  disjoint Y v
  disjoint Y z
  assert |- ( F e. ( G GrpHom H ) -> .(+) e. ( G GrpAct Y ) )

  proof
    cF
    cG
    cH
    cghm
    co
    wcel
    #
    cG
    cgrp
    wcel
    #
    cY
    cvv
    wcel
    #
    wa
    cX
    cY
    cxp
    cY
    c.po
    wf
    #
    cG
    c0g
    cfv
    #
    vz
    cv
    #
    c.po
    co
    #
    @5
    wceq
    #
    vu
    cv
    #
    vv
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @5
    c.po
    co
    #
    @8
    @9
    @5
    c.po
    co
    #
    c.po
    co
    #
    wceq
    #
    vv
    cX
    wral
    vu
    cX
    wral
    #
    wa
    #
    vz
    cY
    wral
    #
    wa
    c.po
    cG
    cY
    cga
    co
    wcel
    @0
    @1
    @2
    cG
    cH
    cF
    ghmgrp1
    #
    @0
    cH
    cgrp
    wcel
    cH
    c0
    wne
    @2
    cG
    cH
    cF
    ghmgrp2
    cH
    grpn0
    @2
    cH
    c0
    @2
    wn
    cH
    cY
    csymg
    cfv
    c0
    lactghmga.h
    cY
    csymg
    fvprc
    syl5eq
    necon1ai
    3syl
    #
    jca
    @0
    @3
    @18
    @0
    vy
    cv
    #
    vx
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cY
    wcel
    #
    vy
    cY
    wral
    #
    vx
    cX
    wral
    @3
    @0
    @26
    vx
    cX
    @0
    @22
    cX
    wcel
    #
    wa
    #
    @25
    vy
    cY
    @28
    cY
    cY
    @21
    @23
    @28
    cY
    cY
    @23
    wf1o
    #
    cY
    cY
    @23
    wf
    @28
    @23
    cH
    cbs
    cfv
    #
    wcel
    #
    @29
    @0
    cX
    @30
    @22
    cF
    cG
    cH
    cF
    cX
    @30
    lactghmga.x
    @30
    eqid
    #
    ghmf
    #
    ffvelrnda
    @28
    @2
    @31
    @29
    wb
    @0
    @2
    @27
    @20
    adantr
    cY
    @30
    @23
    cH
    cvv
    lactghmga.h
    @32
    elsymgbas
    syl
    mpbid
    cY
    cY
    @23
    f1of
    syl
    ffvelrnda
    ralrimiva
    ralrimiva
    vx
    vy
    cX
    cY
    @24
    cY
    c.po
    lactghmga.f
    fmpt2
    sylib
    @0
    @17
    vz
    cY
    @0
    @5
    cY
    wcel
    #
    wa
    #
    @7
    @16
    @35
    @6
    @5
    @4
    cF
    cfv
    #
    cfv
    #
    @5
    cid
    cY
    cres
    #
    cfv
    #
    @5
    @0
    @4
    cX
    wcel
    #
    @34
    @6
    @37
    wceq
    @0
    @1
    @40
    @19
    cX
    cG
    @4
    lactghmga.x
    @4
    eqid
    #
    grpidcl
    syl
    vx
    vy
    @4
    @5
    cX
    cY
    @24
    @37
    c.po
    @21
    @36
    cfv
    @22
    @4
    wceq
    @21
    @23
    @36
    @22
    @4
    cF
    fveq2
    fveq1d
    @21
    @5
    @36
    fveq2
    lactghmga.f
    @5
    @36
    fvex
    ovmpt2
    sylan
    @35
    @5
    @36
    @38
    @35
    @36
    cH
    c0g
    cfv
    #
    @38
    @0
    @36
    @42
    wceq
    @34
    cG
    cH
    cF
    @4
    @42
    @41
    @42
    eqid
    ghmid
    adantr
    @35
    @2
    @38
    @42
    wceq
    @0
    @2
    @34
    @20
    adantr
    cY
    cH
    cvv
    lactghmga.h
    symgid
    syl
    eqtr4d
    fveq1d
    @34
    @39
    @5
    wceq
    @0
    cY
    @5
    fvresi
    adantl
    3eqtrd
    @35
    @15
    vu
    vv
    cX
    cX
    @35
    @8
    cX
    wcel
    #
    @9
    cX
    wcel
    #
    wa
    #
    wa
    #
    @5
    @11
    cF
    cfv
    #
    cfv
    #
    @8
    @5
    @9
    cF
    cfv
    #
    cfv
    #
    c.po
    co
    #
    @12
    @14
    @46
    @5
    @8
    cF
    cfv
    #
    @49
    ccom
    #
    cfv
    #
    @50
    @52
    cfv
    #
    @48
    @51
    @46
    cY
    cY
    @49
    wf
    #
    @34
    @54
    @55
    wceq
    @46
    cY
    cY
    @49
    wf1o
    #
    @56
    @46
    @49
    @30
    wcel
    #
    @57
    @46
    cX
    @30
    @9
    cF
    @0
    cX
    @30
    cF
    wf
    @34
    @45
    @33
    ad2antrr
    #
    @35
    @43
    @44
    simprr
    #
    ffvelrnd
    #
    @46
    @2
    @58
    @57
    wb
    @0
    @2
    @34
    @45
    @20
    ad2antrr
    cY
    @30
    @49
    cH
    cvv
    lactghmga.h
    @32
    elsymgbas
    syl
    mpbid
    cY
    cY
    @49
    f1of
    syl
    #
    @0
    @34
    @45
    simplr
    #
    cY
    cY
    @5
    @52
    @49
    fvco3
    syl2anc
    @46
    @5
    @47
    @53
    @46
    @47
    @52
    @49
    cH
    cplusg
    cfv
    #
    co
    #
    @53
    @46
    @0
    @43
    @44
    @47
    @65
    wceq
    @0
    @34
    @45
    simpll
    @35
    @43
    @44
    simprl
    #
    @60
    @10
    @64
    cG
    cH
    @8
    cF
    @9
    cX
    lactghmga.x
    @10
    eqid
    #
    @64
    eqid
    #
    ghmlin
    syl3anc
    @46
    @52
    @30
    wcel
    @58
    @65
    @53
    wceq
    @46
    cX
    @30
    @8
    cF
    @59
    @66
    ffvelrnd
    @61
    cY
    @30
    @64
    cH
    @52
    @49
    lactghmga.h
    @32
    @68
    symgov
    syl2anc
    eqtrd
    fveq1d
    @46
    @43
    @50
    cY
    wcel
    @51
    @55
    wceq
    @66
    @46
    cY
    cY
    @5
    @49
    @62
    @63
    ffvelrnd
    vx
    vy
    @8
    @50
    cX
    cY
    @24
    @55
    c.po
    @21
    @52
    cfv
    @22
    @8
    wceq
    @21
    @23
    @52
    @22
    @8
    cF
    fveq2
    fveq1d
    @21
    @50
    @52
    fveq2
    lactghmga.f
    @50
    @52
    fvex
    ovmpt2
    syl2anc
    3eqtr4d
    @46
    @11
    cX
    wcel
    #
    @34
    @12
    @48
    wceq
    @46
    @1
    @43
    @44
    @69
    @0
    @1
    @34
    @45
    @19
    ad2antrr
    @66
    @60
    cX
    @10
    cG
    @8
    @9
    lactghmga.x
    @67
    grpcl
    syl3anc
    @63
    vx
    vy
    @11
    @5
    cX
    cY
    @24
    @48
    c.po
    @21
    @47
    cfv
    @22
    @11
    wceq
    @21
    @23
    @47
    @22
    @11
    cF
    fveq2
    fveq1d
    @21
    @5
    @47
    fveq2
    lactghmga.f
    @5
    @47
    fvex
    ovmpt2
    syl2anc
    @46
    @13
    @50
    @8
    c.po
    @46
    @44
    @34
    @13
    @50
    wceq
    @60
    @63
    vx
    vy
    @9
    @5
    cX
    cY
    @24
    @50
    c.po
    @21
    @49
    cfv
    @22
    @9
    wceq
    @21
    @23
    @49
    @22
    @9
    cF
    fveq2
    fveq1d
    @21
    @5
    @49
    fveq2
    lactghmga.f
    @5
    @49
    fvex
    ovmpt2
    syl2anc
    oveq2d
    3eqtr4d
    ralrimivva
    jca
    ralrimiva
    jca
    vz
    vu
    vv
    @10
    c.po
    cG
    cX
    cY
    @4
    lactghmga.x
    @67
    @41
    isga
    sylanbrc
end
