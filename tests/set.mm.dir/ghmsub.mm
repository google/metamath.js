include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "wceq.mm"
include "cgrp.mm"
include "ghmgrp1.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ghmlin.mm"
include "syld3an3.mm"
include "ghminv.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "wa.mm"
include "grpsubval.mm"
include "fveq2d.mm"
include "3adant1.mm"
include "cbs.mm"
include "wf.mm"
include "ghmf.mm"
include "ffvelrn.mm"
include "anim12dan.mm"
include "sylan.mm"
include "3impb.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem ghmsub
  let cB: class B
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let c.mi: class .-
  let cN: class N
  let cV: class V
  assume ghmsub.b: |- B = ( Base ` S )
  assume ghmsub.m: |- .- = ( -g ` S )
  assume ghmsub.n: |- N = ( -g ` T )


  assert |- ( ( F e. ( S GrpHom T ) /\ U e. B /\ V e. B ) -> ( F ` ( U .- V ) ) = ( ( F ` U ) N ( F ` V ) ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cU
    cB
    wcel
    #
    cV
    cB
    wcel
    #
    w3a
    #
    cU
    cV
    cS
    cminusg
    cfv
    #
    cfv
    #
    cS
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    cU
    cF
    cfv
    #
    cV
    cF
    cfv
    #
    cT
    cminusg
    cfv
    #
    cfv
    #
    cT
    cplusg
    cfv
    #
    co
    #
    cU
    cV
    c.mi
    co
    #
    cF
    cfv
    #
    @9
    @10
    cN
    co
    #
    @3
    @8
    @9
    @5
    cF
    cfv
    #
    @13
    co
    #
    @14
    @0
    @1
    @2
    @5
    cB
    wcel
    #
    @8
    @19
    wceq
    @3
    cS
    cgrp
    wcel
    #
    @2
    @20
    @0
    @1
    @21
    @2
    cS
    cT
    cF
    ghmgrp1
    3ad2ant1
    @0
    @1
    @2
    simp3
    cB
    cS
    @4
    cV
    ghmsub.b
    @4
    eqid
    #
    grpinvcl
    syl2anc
    @6
    @13
    cS
    cT
    cU
    cF
    @5
    cB
    ghmsub.b
    @6
    eqid
    #
    @13
    eqid
    #
    ghmlin
    syld3an3
    @3
    @18
    @12
    @9
    @13
    @0
    @2
    @18
    @12
    wceq
    @1
    cB
    cS
    cT
    cF
    @4
    @11
    cV
    ghmsub.b
    @22
    @11
    eqid
    #
    ghminv
    3adant2
    oveq2d
    eqtrd
    @1
    @2
    @16
    @8
    wceq
    @0
    @1
    @2
    wa
    #
    @15
    @7
    cF
    cB
    @6
    cS
    @4
    c.mi
    cU
    cV
    ghmsub.b
    @23
    @22
    ghmsub.m
    grpsubval
    fveq2d
    3adant1
    @3
    @9
    cT
    cbs
    cfv
    #
    wcel
    #
    @10
    @27
    wcel
    #
    wa
    #
    @17
    @14
    wceq
    @0
    @1
    @2
    @30
    @0
    cB
    @27
    cF
    wf
    #
    @26
    @30
    cS
    cT
    cF
    cB
    @27
    ghmsub.b
    @27
    eqid
    #
    ghmf
    @31
    @1
    @28
    @2
    @29
    cB
    @27
    cU
    cF
    ffvelrn
    cB
    @27
    cV
    cF
    ffvelrn
    anim12dan
    sylan
    3impb
    @27
    @13
    cT
    @11
    cN
    @9
    @10
    @32
    @24
    @25
    ghmsub.n
    grpsubval
    syl
    3eqtr4d
end
