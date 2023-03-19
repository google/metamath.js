include "co.mm"
include "cfv.mm"
include "ccnv.mm"
include "invsym2.mm"
include "fveq1d.mm"
include "wf1o.mm"
include "wcel.mm"
include "wceq.mm"
include "invf1o.mm"
include "f1ocnvfv1.mm"
include "syl2anc.mm"
include "eqtr3d.mm"

theorem invinv
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
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
  assume invinv.f: |- ( ph -> F e. ( X I Y ) )


  assert |- ( ph -> ( ( Y N X ) ` ( ( X N Y ) ` F ) ) = F )

  proof
    wph
    cF
    cX
    cY
    cN
    co
    #
    cfv
    #
    @0
    ccnv
    #
    cfv
    #
    @1
    cY
    cX
    cN
    co
    #
    cfv
    cF
    wph
    @1
    @2
    @4
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
    fveq1d
    wph
    cX
    cY
    cI
    co
    #
    cY
    cX
    cI
    co
    #
    @0
    wf1o
    cF
    @5
    wcel
    @3
    cF
    wceq
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
    invf1o
    invinv.f
    @5
    @6
    cF
    @0
    f1ocnvfv1
    syl2anc
    eqtr3d
end
