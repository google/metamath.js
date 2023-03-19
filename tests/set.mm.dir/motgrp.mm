include "cismt.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "cv.mm"
include "ccnv.mm"
include "cid.mm"
include "cres.mm"
include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "wceq.mm"
include "ovex.mm"
include "ccom.mm"
include "cmpt2.mm"
include "grpbase.mm"
include "mp1i.mm"
include "eqidd.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "motplusg.mm"
include "motco.mm"
include "eqeltrd.mm"
include "wa.mm"
include "coass.mm"
include "3adant3r3.mm"
include "oveq1d.mm"
include "adantr.mm"
include "simpr3.mm"
include "eqtrd.mm"
include "simpr2.mm"
include "oveq2d.mm"
include "simpr1.mm"
include "3eqtr4a.mm"
include "idmot.mm"
include "simpr.mm"
include "wf1o.mm"
include "wf.mm"
include "wral.mm"
include "ismot.mm"
include "simprbda.mm"
include "sylan.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "cnvmot.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "isgrpd.mm"

theorem motgrp
  let wph: wff ph
  let cP: class P
  let vf: setvar f
  let vg: setvar g
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cV: class V
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let cH: class H
  let vh: setvar h
  assume ismot.p: |- P = ( Base ` G )
  assume ismot.m: |- .- = ( dist ` G )
  assume motgrp.1: |- ( ph -> G e. V )
  assume motgrp.i: |- I = { <. ( Base ` ndx ) , ( G Ismt G ) >. , <. ( +g ` ndx ) , ( f e. ( G Ismt G ) , g e. ( G Ismt G ) |-> ( f o. g ) ) >. }

  disjoint G f
  disjoint G g
  disjoint f g
  disjoint I f
  disjoint I g
  disjoint P f
  disjoint P g
  disjoint f ph
  disjoint g ph
  disjoint F a
  disjoint F b
  disjoint a b
  disjoint G a
  disjoint G b
  disjoint P a
  disjoint P b
  disjoint a f
  disjoint a g
  disjoint b f
  disjoint b g
  disjoint H a
  disjoint H b
  disjoint a ph
  disjoint b ph
  disjoint G h
  disjoint f h
  disjoint g h
  disjoint I h
  disjoint P h
  disjoint a h
  disjoint b h
  disjoint h ph
  assert |- ( ph -> I e. Grp )

  proof
    wph
    vf
    vg
    vh
    cG
    cG
    cismt
    co
    #
    cI
    cplusg
    cfv
    #
    cI
    vf
    cv
    #
    ccnv
    #
    cid
    cP
    cres
    #
    @0
    cvv
    wcel
    @0
    cI
    cbs
    cfv
    wceq
    wph
    cG
    cG
    cismt
    ovex
    @0
    vf
    vg
    @0
    @0
    @2
    vg
    cv
    #
    ccom
    #
    cmpt2
    cI
    cvv
    motgrp.i
    grpbase
    mp1i
    wph
    @1
    eqidd
    wph
    @2
    @0
    wcel
    #
    @5
    @0
    wcel
    #
    w3a
    #
    @2
    @5
    @1
    co
    #
    @6
    @0
    @9
    cP
    vf
    vg
    @2
    cG
    @5
    cI
    c.mi
    cV
    ismot.p
    ismot.m
    wph
    @7
    cG
    cV
    wcel
    #
    @8
    motgrp.1
    3ad2ant1
    #
    motgrp.i
    wph
    @7
    @8
    simp2
    #
    wph
    @7
    @8
    simp3
    #
    motplusg
    #
    @9
    cP
    @2
    cG
    @5
    c.mi
    cV
    ismot.p
    ismot.m
    @12
    @13
    @14
    motco
    #
    eqeltrd
    wph
    @7
    @8
    vh
    cv
    #
    @0
    wcel
    #
    w3a
    #
    wa
    #
    @6
    @17
    ccom
    #
    @2
    @5
    @17
    ccom
    #
    ccom
    #
    @10
    @17
    @1
    co
    #
    @2
    @5
    @17
    @1
    co
    #
    @1
    co
    #
    @2
    @5
    @17
    coass
    @20
    @24
    @6
    @17
    @1
    co
    @21
    @20
    @10
    @6
    @17
    @1
    wph
    @7
    @8
    @10
    @6
    wceq
    @18
    @15
    3adant3r3
    oveq1d
    @20
    cP
    vf
    vg
    @6
    cG
    @17
    cI
    c.mi
    cV
    ismot.p
    ismot.m
    wph
    @11
    @19
    motgrp.1
    adantr
    #
    motgrp.i
    wph
    @7
    @8
    @6
    @0
    wcel
    @18
    @16
    3adant3r3
    wph
    @7
    @8
    @18
    simpr3
    #
    motplusg
    eqtrd
    @20
    @26
    @2
    @22
    @1
    co
    @23
    @20
    @25
    @22
    @2
    @1
    @20
    cP
    vf
    vg
    @5
    cG
    @17
    cI
    c.mi
    cV
    ismot.p
    ismot.m
    @27
    motgrp.i
    wph
    @7
    @8
    @18
    simpr2
    #
    @28
    motplusg
    oveq2d
    @20
    cP
    vf
    vg
    @2
    cG
    @22
    cI
    c.mi
    cV
    ismot.p
    ismot.m
    @27
    motgrp.i
    wph
    @7
    @8
    @18
    simpr1
    @20
    cP
    @5
    cG
    @17
    c.mi
    cV
    ismot.p
    ismot.m
    @27
    @29
    @28
    motco
    motplusg
    eqtrd
    3eqtr4a
    wph
    cP
    cG
    c.mi
    cV
    ismot.p
    ismot.m
    motgrp.1
    idmot
    #
    wph
    @7
    wa
    #
    @4
    @2
    @1
    co
    @4
    @2
    ccom
    #
    @2
    @31
    cP
    vf
    vg
    @4
    cG
    @2
    cI
    c.mi
    cV
    ismot.p
    ismot.m
    wph
    @11
    @7
    motgrp.1
    adantr
    #
    motgrp.i
    wph
    @4
    @0
    wcel
    @7
    @30
    adantr
    wph
    @7
    simpr
    #
    motplusg
    @31
    cP
    cP
    @2
    wf1o
    #
    cP
    cP
    @2
    wf
    @32
    @2
    wceq
    wph
    @11
    @7
    @35
    motgrp.1
    @11
    @7
    @35
    va
    cv
    #
    @2
    cfv
    vb
    cv
    #
    @2
    cfv
    c.mi
    co
    @36
    @37
    c.mi
    co
    wceq
    vb
    cP
    wral
    va
    cP
    wral
    cP
    @2
    cG
    c.mi
    cV
    va
    vb
    ismot.p
    ismot.m
    ismot
    simprbda
    sylan
    #
    cP
    cP
    @2
    f1of
    cP
    cP
    @2
    fcoi2
    3syl
    eqtrd
    @31
    cP
    @2
    cG
    c.mi
    cV
    ismot.p
    ismot.m
    @33
    @34
    cnvmot
    #
    @31
    @3
    @2
    @1
    co
    @3
    @2
    ccom
    #
    @4
    @31
    cP
    vf
    vg
    @3
    cG
    @2
    cI
    c.mi
    cV
    ismot.p
    ismot.m
    @33
    motgrp.i
    @39
    @34
    motplusg
    @31
    @35
    @40
    @4
    wceq
    @38
    cP
    cP
    @2
    f1ococnv1
    syl
    eqtrd
    isgrpd
end
