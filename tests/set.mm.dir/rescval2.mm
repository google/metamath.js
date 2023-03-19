include "cdm.mm"
include "cress.mm"
include "co.mm"
include "cnx.mm"
include "chom.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "wcel.mm"
include "cvv.mm"
include "wceq.mm"
include "cxp.mm"
include "wfn.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "fnex.mm"
include "rescval.mm"
include "fndm.mm"
include "syl.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem rescval2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cH: class H
  let cV: class V
  let cW: class W
  let vc: setvar c
  let vh: setvar h
  assume rescval.1: |- D = ( C |`cat H )
  assume rescval2.1: |- ( ph -> C e. V )
  assume rescval2.2: |- ( ph -> S e. W )
  assume rescval2.3: |- ( ph -> H Fn ( S X. S ) )


  assert |- ( ph -> D = ( ( C |`s S ) sSet <. ( Hom ` ndx ) , H >. ) )

  proof
    wph
    cD
    cC
    cH
    cdm
    #
    cdm
    #
    cress
    co
    #
    cnx
    chom
    cfv
    cH
    cop
    #
    csts
    co
    #
    cC
    cS
    cress
    co
    #
    @3
    csts
    co
    wph
    cC
    cV
    wcel
    cH
    cvv
    wcel
    #
    cD
    @4
    wceq
    rescval2.1
    wph
    cH
    cS
    cS
    cxp
    #
    wfn
    #
    @7
    cvv
    wcel
    #
    @6
    rescval2.3
    wph
    cS
    cW
    wcel
    #
    @10
    @9
    rescval2.2
    rescval2.2
    cS
    cS
    cW
    cW
    xpexg
    syl2anc
    @7
    cvv
    cH
    fnex
    syl2anc
    cC
    cD
    cH
    cV
    cvv
    rescval.1
    rescval
    syl2anc
    wph
    @2
    @5
    @3
    csts
    wph
    @1
    cS
    cC
    cress
    wph
    @1
    @7
    cdm
    cS
    wph
    @0
    @7
    wph
    @8
    @0
    @7
    wceq
    rescval2.3
    @7
    cH
    fndm
    syl
    dmeqd
    cS
    dmxpid
    syl6eq
    oveq2d
    oveq1d
    eqtrd
end
