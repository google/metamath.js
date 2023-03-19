include "co.mm"
include "csect.mm"
include "cfv.mm"
include "cxp.mm"
include "ccnv.mm"
include "cin.mm"
include "eqid.mm"
include "invfval.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "cco.mm"
include "ccid.mm"
include "sectss.mm"
include "sstrd.mm"

theorem invss
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cH: class H
  let cN: class N
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vz: setvar z
  let cS: class S
  assume invfval.b: |- B = ( Base ` C )
  assume invfval.n: |- N = ( Inv ` C )
  assume invfval.c: |- ( ph -> C e. Cat )
  assume invfval.x: |- ( ph -> X e. B )
  assume invfval.y: |- ( ph -> Y e. B )
  assume invss.h: |- H = ( Hom ` C )


  assert |- ( ph -> ( X N Y ) C_ ( ( X H Y ) X. ( Y H X ) ) )

  proof
    wph
    cX
    cY
    cN
    co
    #
    cX
    cY
    cC
    csect
    cfv
    #
    co
    #
    cX
    cY
    cH
    co
    cY
    cX
    cH
    co
    cxp
    wph
    @0
    @2
    cY
    cX
    @1
    co
    ccnv
    #
    cin
    @2
    wph
    cB
    cC
    @1
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    @1
    eqid
    #
    invfval
    @2
    @3
    inss1
    syl6eqss
    wph
    cB
    cC
    @1
    cC
    cco
    cfv
    #
    cC
    ccid
    cfv
    #
    cH
    cX
    cY
    invfval.b
    invss.h
    @5
    eqid
    @6
    eqid
    @4
    invfval.c
    invfval.x
    invfval.y
    sectss
    sstrd
end
