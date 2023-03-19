include "co.mm"
include "wfn.mm"
include "ccnv.mm"
include "wf1o.mm"
include "wf.mm"
include "invf.mm"
include "ffn.mm"
include "syl.mm"
include "invsym2.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "dff1o4.mm"
include "sylanbrc.mm"

theorem invf1o
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


  assert |- ( ph -> ( X N Y ) : ( X I Y ) -1-1-onto-> ( Y I X ) )

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
    ccnv
    #
    cY
    cX
    cI
    co
    #
    wfn
    #
    @1
    @4
    @0
    wf1o
    wph
    @1
    @4
    @0
    wf
    @2
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
    invf
    @1
    @4
    @0
    ffn
    syl
    wph
    @5
    cY
    cX
    cN
    co
    #
    @4
    wfn
    #
    wph
    @4
    @1
    @6
    wf
    @7
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
    invf
    @4
    @1
    @6
    ffn
    syl
    wph
    @4
    @3
    @6
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
    fneq1d
    mpbird
    @1
    @4
    @0
    dff1o4
    sylanbrc
end
