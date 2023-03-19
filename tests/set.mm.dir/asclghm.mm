include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "crg.mm"
include "wcel.mm"
include "cgrp.mm"
include "clmod.mm"
include "lmodring.mm"
include "syl.mm"
include "ringgrp.mm"
include "asclf.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "cur.mm"
include "cvsca.mm"
include "wceq.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "ringidcl.mm"
include "lmodvsdir.mm"
include "syl13anc.mm"
include "grpcl.mm"
include "3expb.mm"
include "sylan.mm"
include "asclval.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "isghmd.mm"

theorem asclghm
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  assume asclf.a: |- A = ( algSc ` W )
  assume asclf.f: |- F = ( Scalar ` W )
  assume asclf.r: |- ( ph -> W e. Ring )
  assume asclf.l: |- ( ph -> W e. LMod )


  assert |- ( ph -> A e. ( F GrpHom W ) )

  proof
    wph
    vx
    vy
    cF
    cplusg
    cfv
    #
    cW
    cplusg
    cfv
    #
    cF
    cW
    cA
    cF
    cbs
    cfv
    #
    cW
    cbs
    cfv
    #
    @2
    eqid
    #
    @3
    eqid
    #
    @0
    eqid
    #
    @1
    eqid
    #
    wph
    cF
    crg
    wcel
    #
    cF
    cgrp
    wcel
    #
    wph
    cW
    clmod
    wcel
    #
    @8
    asclf.l
    cF
    cW
    asclf.f
    lmodring
    syl
    cF
    ringgrp
    syl
    #
    wph
    cW
    crg
    wcel
    #
    cW
    cgrp
    wcel
    asclf.r
    cW
    ringgrp
    syl
    wph
    cA
    @3
    cF
    @2
    cW
    asclf.a
    asclf.f
    asclf.r
    asclf.l
    @4
    @5
    asclf
    wph
    vx
    cv
    #
    @2
    wcel
    #
    vy
    cv
    #
    @2
    wcel
    #
    wa
    #
    wa
    #
    @13
    @15
    @0
    co
    #
    cW
    cur
    cfv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    @13
    @20
    @21
    co
    #
    @15
    @20
    @21
    co
    #
    @1
    co
    #
    @19
    cA
    cfv
    #
    @13
    cA
    cfv
    #
    @15
    cA
    cfv
    #
    @1
    co
    #
    @18
    @10
    @14
    @16
    @20
    @3
    wcel
    #
    @22
    @25
    wceq
    wph
    @10
    @17
    asclf.l
    adantr
    wph
    @14
    @16
    simprl
    wph
    @14
    @16
    simprr
    wph
    @30
    @17
    wph
    @12
    @30
    asclf.r
    @3
    cW
    @20
    @5
    @20
    eqid
    #
    ringidcl
    syl
    adantr
    @1
    @0
    @13
    @15
    @21
    cF
    @2
    @3
    cW
    @20
    @5
    @7
    asclf.f
    @21
    eqid
    #
    @4
    @6
    lmodvsdir
    syl13anc
    @18
    @19
    @2
    wcel
    #
    @26
    @22
    wceq
    wph
    @9
    @17
    @33
    @11
    @9
    @14
    @16
    @33
    @2
    @0
    cF
    @13
    @15
    @4
    @6
    grpcl
    3expb
    sylan
    cA
    @21
    @20
    cF
    @2
    cW
    @19
    asclf.a
    asclf.f
    @4
    @32
    @31
    asclval
    syl
    @17
    @29
    @25
    wceq
    wph
    @14
    @16
    @27
    @23
    @28
    @24
    @1
    cA
    @21
    @20
    cF
    @2
    cW
    @13
    asclf.a
    asclf.f
    @4
    @32
    @31
    asclval
    cA
    @21
    @20
    cF
    @2
    cW
    @15
    asclf.a
    asclf.f
    @4
    @32
    @31
    asclval
    oveqan12d
    adantl
    3eqtr4d
    isghmd
end
