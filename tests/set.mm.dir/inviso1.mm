include "co.mm"
include "cdm.mm"
include "wrel.mm"
include "wbr.mm"
include "wcel.mm"
include "wfun.mm"
include "invfun.mm"
include "funrel.mm"
include "syl.mm"
include "releldm.mm"
include "syl2anc.mm"
include "isoval.mm"
include "eleqtrrd.mm"

theorem inviso1
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


  assert |- ( ph -> F e. ( X I Y ) )

  proof
    wph
    cF
    cX
    cY
    cN
    co
    #
    cdm
    #
    cX
    cY
    cI
    co
    wph
    @0
    wrel
    #
    cF
    cG
    @0
    wbr
    cF
    @1
    wcel
    wph
    @0
    wfun
    @2
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
    funrel
    syl
    inviso1.1
    cF
    cG
    @0
    releldm
    syl2anc
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
    eleqtrrd
end
