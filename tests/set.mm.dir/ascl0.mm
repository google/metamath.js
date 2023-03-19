include "c0g.mm"
include "cfv.mm"
include "cur.mm"
include "cvsca.mm"
include "co.mm"
include "cbs.mm"
include "wcel.mm"
include "wceq.mm"
include "cgrp.mm"
include "clmod.mm"
include "lmodfgrp.mm"
include "syl.mm"
include "eqid.mm"
include "grpidcl.mm"
include "asclval.mm"
include "crg.mm"
include "ringidcl.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem ascl0
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cW: class W
  let vk: setvar k
  let vx: setvar x
  assume ascl0.a: |- A = ( algSc ` W )
  assume ascl0.f: |- F = ( Scalar ` W )
  assume ascl0.l: |- ( ph -> W e. LMod )
  assume ascl0.r: |- ( ph -> W e. Ring )


  assert |- ( ph -> ( A ` ( 0g ` F ) ) = ( 0g ` W ) )

  proof
    wph
    cF
    c0g
    cfv
    #
    cA
    cfv
    #
    @0
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
    cW
    c0g
    cfv
    #
    wph
    @0
    cF
    cbs
    cfv
    #
    wcel
    #
    @1
    @4
    wceq
    wph
    cF
    cgrp
    wcel
    #
    @7
    wph
    cW
    clmod
    wcel
    #
    @8
    ascl0.l
    cF
    cW
    ascl0.f
    lmodfgrp
    syl
    @6
    cF
    @0
    @6
    eqid
    #
    @0
    eqid
    #
    grpidcl
    syl
    cA
    @3
    @2
    cF
    @6
    cW
    @0
    ascl0.a
    ascl0.f
    @10
    @3
    eqid
    #
    @2
    eqid
    #
    asclval
    syl
    wph
    @9
    @2
    cW
    cbs
    cfv
    #
    wcel
    #
    @4
    @5
    wceq
    ascl0.l
    wph
    cW
    crg
    wcel
    @15
    ascl0.r
    @14
    cW
    @2
    @14
    eqid
    #
    @13
    ringidcl
    syl
    @3
    cF
    @0
    @14
    cW
    @2
    @5
    @16
    ascl0.f
    @12
    @11
    @5
    eqid
    lmod0vs
    syl2anc
    eqtrd
end
