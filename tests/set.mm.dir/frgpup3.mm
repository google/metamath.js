include "cgrp.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "cid.mm"
include "cfv.mm"
include "cv.mm"
include "cefg.mm"
include "cec.mm"
include "c0.mm"
include "wceq.mm"
include "cminusg.mm"
include "cif.mm"
include "cmpt2.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "cop.mm"
include "cmpt.mm"
include "crn.mm"
include "cghm.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "cbs.mm"
include "eqid.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "frgpup1.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "frgpup2.mm"
include "mpteq2dva.mm"
include "ghmf.mm"
include "syl.mm"
include "vrgpf.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "feqmptd.mm"
include "3eqtr4d.mm"
include "simprl.mm"
include "simprr.mm"
include "frgpup3lem.mm"
include "expr.mm"
include "ralrimiva.mm"
include "coeq1.mm"
include "eqeq1d.mm"
include "eqreu.mm"
include "syl3anc.mm"

theorem frgpup3
  let cB: class B
  let cU: class U
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cV: class V
  let vg: setvar g
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  assume frgpup3.g: |- G = ( freeGrp ` I )
  assume frgpup3.b: |- B = ( Base ` H )
  assume frgpup3.u: |- U = ( varFGrp ` I )

  disjoint B m
  disjoint F m
  disjoint G m
  disjoint H m
  disjoint I m
  disjoint U m
  disjoint V m
  disjoint g k
  disjoint g m
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint m y
  disjoint m z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F g
  disjoint F k
  disjoint F y
  disjoint F z
  disjoint G g
  disjoint G k
  disjoint G y
  disjoint G z
  disjoint H g
  disjoint H k
  disjoint H y
  disjoint H z
  disjoint I g
  disjoint I k
  disjoint I y
  disjoint I z
  disjoint U g
  disjoint U k
  disjoint U y
  disjoint U z
  disjoint V g
  disjoint V k
  disjoint V y
  disjoint V z
  assert |- ( ( H e. Grp /\ I e. V /\ F : I --> B ) -> E! m e. ( G GrpHom H ) ( m o. U ) = F )

  proof
    cH
    cgrp
    wcel
    #
    cI
    cV
    wcel
    #
    cI
    cB
    cF
    wf
    #
    w3a
    #
    vg
    cI
    c2o
    cxp
    cword
    cid
    cfv
    #
    vg
    cv
    #
    cI
    cefg
    cfv
    #
    cec
    cH
    vy
    vz
    cI
    c2o
    vz
    cv
    c0
    wceq
    vy
    cv
    cF
    cfv
    #
    @7
    cH
    cminusg
    cfv
    #
    cfv
    cif
    cmpt2
    #
    @5
    ccom
    cgsu
    co
    cop
    cmpt
    crn
    #
    cG
    cH
    cghm
    co
    #
    wcel
    #
    @10
    cU
    ccom
    #
    cF
    wceq
    #
    vm
    cv
    #
    cU
    ccom
    #
    cF
    wceq
    #
    @15
    @10
    wceq
    #
    wi
    #
    vm
    @11
    wral
    @17
    vm
    @11
    wreu
    @3
    vy
    vz
    cB
    @6
    @9
    vg
    @10
    cF
    cG
    cH
    cI
    @8
    cV
    @4
    cG
    cbs
    cfv
    #
    frgpup3.b
    @8
    eqid
    #
    @9
    eqid
    #
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    #
    @4
    eqid
    #
    @6
    eqid
    #
    frgpup3.g
    @20
    eqid
    #
    @10
    eqid
    #
    frgpup1
    #
    @3
    vk
    cI
    vk
    cv
    #
    cU
    cfv
    @10
    cfv
    #
    cmpt
    #
    vk
    cI
    @31
    cF
    cfv
    #
    cmpt
    @13
    cF
    @3
    vk
    cI
    @32
    @34
    @3
    @31
    cI
    wcel
    #
    wa
    vy
    vz
    @31
    cB
    @6
    @9
    cU
    vg
    @10
    cF
    cG
    cH
    cI
    @8
    cV
    @4
    @20
    frgpup3.b
    @21
    @22
    @3
    @0
    @35
    @23
    adantr
    @3
    @1
    @35
    @24
    adantr
    @3
    @2
    @35
    @25
    adantr
    @26
    @27
    frgpup3.g
    @28
    @29
    frgpup3.u
    @3
    @35
    simpr
    frgpup2
    mpteq2dva
    @3
    @20
    cB
    @10
    wf
    #
    cI
    @20
    cU
    wf
    #
    @13
    @33
    wceq
    @3
    @12
    @36
    @30
    cG
    cH
    @10
    @20
    cB
    @28
    frgpup3.b
    ghmf
    syl
    @3
    @1
    @37
    @24
    @6
    cU
    cG
    cI
    cV
    @20
    @27
    frgpup3.u
    frgpup3.g
    @28
    vrgpf
    syl
    vk
    @10
    cU
    cI
    @20
    cB
    fcompt
    syl2anc
    @3
    vk
    cI
    cB
    cF
    @25
    feqmptd
    3eqtr4d
    @3
    @19
    vm
    @11
    @3
    @15
    @11
    wcel
    #
    @17
    @18
    @3
    @38
    @17
    wa
    #
    wa
    vy
    vz
    cB
    @6
    @9
    cU
    vg
    @10
    cF
    cG
    cH
    cI
    @15
    @8
    cV
    @4
    @20
    frgpup3.b
    @21
    @22
    @3
    @0
    @39
    @23
    adantr
    @3
    @1
    @39
    @24
    adantr
    @3
    @2
    @39
    @25
    adantr
    @26
    @27
    frgpup3.g
    @28
    @29
    frgpup3.u
    @3
    @38
    @17
    simprl
    @3
    @38
    @17
    simprr
    frgpup3lem
    expr
    ralrimiva
    @17
    @14
    vm
    @11
    @10
    @18
    @16
    @13
    cF
    @15
    @10
    cU
    coeq1
    eqeq1d
    eqreu
    syl3anc
end
