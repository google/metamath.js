include "csca.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "cvv.mm"
include "cpws.mm"
include "cmpt.mm"
include "cprds.mm"
include "csn.mm"
include "cxp.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "pwsval.mm"
include "syl2anc.mm"
include "fconstmpt.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "ovex.mm"
include "sylancr.mm"
include "fvexd.mm"
include "cv.mm"
include "adantr.mm"
include "ressprdsds.mm"

theorem resspwsds
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cE: class E
  let cH: class H
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume resspwsds.y: |- ( ph -> Y = ( R ^s I ) )
  assume resspwsds.h: |- ( ph -> H = ( ( R |`s A ) ^s I ) )
  assume resspwsds.b: |- B = ( Base ` H )
  assume resspwsds.d: |- D = ( dist ` Y )
  assume resspwsds.e: |- E = ( dist ` H )
  assume resspwsds.i: |- ( ph -> I e. V )
  assume resspwsds.r: |- ( ph -> R e. W )
  assume resspwsds.a: |- ( ph -> A e. X )


  assert |- ( ph -> E = ( D |` ( B X. B ) ) )

  proof
    wph
    vx
    cA
    cB
    cD
    cR
    cR
    csca
    cfv
    #
    cR
    cA
    cress
    co
    #
    csca
    cfv
    #
    cvv
    cE
    cH
    cI
    cvv
    cV
    cW
    cY
    cX
    wph
    cY
    cR
    cI
    cpws
    co
    #
    @0
    vx
    cI
    cR
    cmpt
    #
    cprds
    co
    #
    resspwsds.y
    wph
    @3
    @0
    cI
    cR
    csn
    cxp
    #
    cprds
    co
    #
    @5
    wph
    cR
    cW
    wcel
    #
    cI
    cV
    wcel
    #
    @3
    @7
    wceq
    resspwsds.r
    resspwsds.i
    cR
    @0
    cI
    cW
    cV
    @3
    @3
    eqid
    @0
    eqid
    pwsval
    syl2anc
    @6
    @4
    @0
    cprds
    vx
    cI
    cR
    fconstmpt
    oveq2i
    syl6eq
    eqtrd
    wph
    cH
    @1
    cI
    cpws
    co
    #
    @2
    vx
    cI
    @1
    cmpt
    #
    cprds
    co
    #
    resspwsds.h
    wph
    @10
    @2
    cI
    @1
    csn
    cxp
    #
    cprds
    co
    #
    @12
    wph
    @1
    cvv
    wcel
    @9
    @10
    @14
    wceq
    cR
    cA
    cress
    ovex
    resspwsds.i
    @1
    @2
    cI
    cvv
    cV
    @10
    @10
    eqid
    @2
    eqid
    pwsval
    sylancr
    @13
    @11
    @2
    cprds
    vx
    cI
    @1
    fconstmpt
    oveq2i
    syl6eq
    eqtrd
    resspwsds.b
    resspwsds.d
    resspwsds.e
    wph
    cR
    csca
    fvexd
    wph
    @1
    csca
    fvexd
    resspwsds.i
    wph
    @8
    vx
    cv
    cI
    wcel
    #
    resspwsds.r
    adantr
    wph
    cA
    cX
    wcel
    @15
    resspwsds.a
    adantr
    ressprdsds
end
