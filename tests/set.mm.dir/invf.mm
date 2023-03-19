include "co.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wf.mm"
include "cdm.mm"
include "wfun.mm"
include "invfun.mm"
include "funfn.mm"
include "sylib.mm"
include "isoval.mm"
include "fneq2d.mm"
include "mpbird.mm"
include "wceq.mm"
include "ccnv.mm"
include "df-rn.mm"
include "invsym2.mm"
include "dmeqd.mm"
include "eqtr4d.mm"
include "syl5eq.mm"
include "eqimss.mm"
include "syl.mm"
include "df-f.mm"
include "sylanbrc.mm"

theorem invf
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cI: class I
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
  assume isoval.n: |- I = ( Iso ` C )


  assert |- ( ph -> ( X N Y ) : ( X I Y ) --> ( Y I X ) )

  proof
    wph
    cX
    cY
    cN
    co
    #
    cX
    cY
    cI
    co
    #
    wfn
    #
    @0
    crn
    #
    cY
    cX
    cI
    co
    #
    wss
    #
    @1
    @4
    @0
    wf
    wph
    @2
    @0
    @0
    cdm
    #
    wfn
    #
    wph
    @0
    wfun
    @7
    wph
    cB
    cC
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    invfun
    @0
    funfn
    sylib
    wph
    @1
    @6
    @0
    wph
    cB
    cC
    cI
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    isoval.n
    isoval
    fneq2d
    mpbird
    wph
    @3
    @4
    wceq
    @5
    wph
    @3
    @0
    ccnv
    #
    cdm
    #
    @4
    @0
    df-rn
    wph
    @9
    cY
    cX
    cN
    co
    #
    cdm
    @4
    wph
    @8
    @10
    wph
    cB
    cC
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    invsym2
    dmeqd
    wph
    cB
    cC
    cI
    cN
    cY
    cX
    invfval.b
    invfval.n
    invfval.c
    invfval.y
    invfval.x
    isoval.n
    isoval
    eqtr4d
    syl5eq
    @3
    @4
    eqimss
    syl
    @1
    @4
    @0
    df-f
    sylanbrc
end
