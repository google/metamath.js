include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "cv.mm"
include "ccnv.mm"
include "cid.mm"
include "cres.mm"
include "eqidd.mm"
include "co.mm"
include "eqid.mm"
include "symgcl.mm"
include "3adant1.mm"
include "w3a.mm"
include "wa.mm"
include "ccom.mm"
include "coass.mm"
include "wceq.mm"
include "simpr1.mm"
include "simpr2.mm"
include "symgov.mm"
include "syl2anc.mm"
include "coeq1d.mm"
include "simpr3.mm"
include "coeq2d.mm"
include "3eqtr4a.mm"
include "3eqtr4d.mm"
include "wf1o.mm"
include "f1oi.mm"
include "elsymgbas.mm"
include "mpbiri.mm"
include "sylan.mm"
include "wf.mm"
include "biimpa.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "eqtrd.mm"
include "wi.mm"
include "f1ocnv.mm"
include "a1i.mm"
include "3imtr4d.mm"
include "imp.mm"
include "sylancom.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "isgrpd.mm"

theorem symggrp
  let cA: class A
  let cG: class G
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume symggrp.1: |- G = ( SymGrp ` A )


  assert |- ( A e. V -> G e. Grp )

  proof
    cA
    cV
    wcel
    #
    vx
    vy
    vz
    cG
    cbs
    cfv
    #
    cG
    cplusg
    cfv
    #
    cG
    vx
    cv
    #
    ccnv
    #
    cid
    cA
    cres
    #
    @0
    @1
    eqidd
    @0
    @2
    eqidd
    @3
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    @3
    @7
    @2
    co
    #
    @1
    wcel
    #
    @0
    cA
    @1
    @2
    cG
    @3
    @7
    symggrp.1
    @1
    eqid
    #
    @2
    eqid
    #
    symgcl
    #
    3adant1
    @0
    @6
    @8
    vz
    cv
    #
    @1
    wcel
    #
    w3a
    wa
    #
    @9
    @14
    ccom
    #
    @3
    @7
    @14
    @2
    co
    #
    ccom
    #
    @9
    @14
    @2
    co
    #
    @3
    @18
    @2
    co
    #
    @16
    @3
    @7
    ccom
    #
    @14
    ccom
    @3
    @7
    @14
    ccom
    #
    ccom
    @17
    @19
    @3
    @7
    @14
    coass
    @16
    @9
    @22
    @14
    @16
    @6
    @8
    @9
    @22
    wceq
    @0
    @6
    @8
    @15
    simpr1
    #
    @0
    @6
    @8
    @15
    simpr2
    #
    cA
    @1
    @2
    cG
    @3
    @7
    symggrp.1
    @11
    @12
    symgov
    syl2anc
    coeq1d
    @16
    @18
    @23
    @3
    @16
    @8
    @15
    @18
    @23
    wceq
    @25
    @0
    @6
    @8
    @15
    simpr3
    #
    cA
    @1
    @2
    cG
    @7
    @14
    symggrp.1
    @11
    @12
    symgov
    syl2anc
    coeq2d
    3eqtr4a
    @16
    @10
    @15
    @20
    @17
    wceq
    @16
    @6
    @8
    @10
    @24
    @25
    @13
    syl2anc
    @26
    cA
    @1
    @2
    cG
    @9
    @14
    symggrp.1
    @11
    @12
    symgov
    syl2anc
    @16
    @6
    @18
    @1
    wcel
    #
    @21
    @19
    wceq
    @24
    @16
    @8
    @15
    @27
    @25
    @26
    cA
    @1
    @2
    cG
    @7
    @14
    symggrp.1
    @11
    @12
    symgcl
    syl2anc
    cA
    @1
    @2
    cG
    @3
    @18
    symggrp.1
    @11
    @12
    symgov
    syl2anc
    3eqtr4d
    @0
    @5
    @1
    wcel
    #
    cA
    cA
    @5
    wf1o
    cA
    f1oi
    cA
    @1
    @5
    cG
    cV
    symggrp.1
    @11
    elsymgbas
    mpbiri
    #
    @0
    @6
    wa
    #
    @5
    @3
    @2
    co
    #
    @5
    @3
    ccom
    #
    @3
    @0
    @28
    @6
    @31
    @32
    wceq
    @29
    cA
    @1
    @2
    cG
    @5
    @3
    symggrp.1
    @11
    @12
    symgov
    sylan
    @30
    cA
    cA
    @3
    wf1o
    #
    cA
    cA
    @3
    wf
    @32
    @3
    wceq
    @0
    @6
    @33
    cA
    @1
    @3
    cG
    cV
    symggrp.1
    @11
    elsymgbas
    #
    biimpa
    #
    cA
    cA
    @3
    f1of
    cA
    cA
    @3
    fcoi2
    3syl
    eqtrd
    @0
    @6
    @4
    @1
    wcel
    #
    @0
    @33
    cA
    cA
    @4
    wf1o
    #
    @6
    @36
    @33
    @37
    wi
    @0
    cA
    cA
    @3
    f1ocnv
    a1i
    @34
    cA
    @1
    @4
    cG
    cV
    symggrp.1
    @11
    elsymgbas
    3imtr4d
    imp
    #
    @30
    @4
    @3
    @2
    co
    #
    @4
    @3
    ccom
    #
    @5
    @0
    @6
    @36
    @39
    @40
    wceq
    @38
    cA
    @1
    @2
    cG
    @4
    @3
    symggrp.1
    @11
    @12
    symgov
    sylancom
    @30
    @33
    @40
    @5
    wceq
    @35
    cA
    cA
    @3
    f1ococnv1
    syl
    eqtrd
    isgrpd
end
