include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cfv.mm"
include "wceq.mm"
include "copab.mm"
include "w3a.mm"
include "sectfval.mm"
include "breqd.mm"
include "oveq12.mm"
include "ancoms.mm"
include "eqeq1d.mm"
include "eqid.mm"
include "brab2a.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem issect
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  assume issect.b: |- B = ( Base ` C )
  assume issect.h: |- H = ( Hom ` C )
  assume issect.o: |- .x. = ( comp ` C )
  assume issect.i: |- .1. = ( Id ` C )
  assume issect.s: |- S = ( Sect ` C )
  assume issect.c: |- ( ph -> C e. Cat )
  assume issect.x: |- ( ph -> X e. B )
  assume issect.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( F ( X S Y ) G <-> ( F e. ( X H Y ) /\ G e. ( Y H X ) /\ ( G ( <. X , Y >. .x. X ) F ) = ( .1. ` X ) ) ) )

  proof
    wph
    cF
    cG
    cX
    cY
    cS
    co
    #
    wbr
    cF
    cG
    vf
    cv
    #
    cX
    cY
    cH
    co
    #
    wcel
    vg
    cv
    #
    cY
    cX
    cH
    co
    #
    wcel
    wa
    @3
    @1
    cX
    cY
    cop
    cX
    c.x
    co
    #
    co
    #
    cX
    c.1
    cfv
    #
    wceq
    #
    wa
    vf
    vg
    copab
    #
    wbr
    #
    cF
    @2
    wcel
    #
    cG
    @4
    wcel
    #
    cG
    cF
    @5
    co
    #
    @7
    wceq
    #
    w3a
    #
    wph
    @0
    @9
    cF
    cG
    wph
    cB
    cC
    cS
    c.x
    c.1
    vf
    vg
    cH
    cX
    cY
    issect.b
    issect.h
    issect.o
    issect.i
    issect.s
    issect.c
    issect.x
    issect.y
    sectfval
    breqd
    @10
    @11
    @12
    wa
    @14
    wa
    @15
    @8
    @14
    vf
    vg
    cF
    cG
    @2
    @4
    @9
    @1
    cF
    wceq
    #
    @3
    cG
    wceq
    #
    wa
    @6
    @13
    @7
    @17
    @16
    @6
    @13
    wceq
    @3
    cG
    @1
    cF
    @5
    oveq12
    ancoms
    eqeq1d
    @9
    eqid
    brab2a
    @11
    @12
    @14
    df-3an
    bitr4i
    syl6bb
end
