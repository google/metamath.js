include "co.mm"
include "wbr.mm"
include "invsym.mm"
include "mpbid.mm"
include "inviso1.mm"

theorem inviso2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
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
  assume inviso1.1: |- ( ph -> F ( X N Y ) G )


  assert |- ( ph -> G e. ( Y I X ) )

  proof
    wph
    cB
    cC
    cG
    cF
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
    wph
    cF
    cG
    cX
    cY
    cN
    co
    wbr
    cG
    cF
    cY
    cX
    cN
    co
    wbr
    inviso1.1
    wph
    cB
    cC
    cF
    cG
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    invsym
    mpbid
    inviso1
end
