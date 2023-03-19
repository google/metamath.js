include "cfv.mm"
include "crg.mm"
include "wcel.mm"
include "wne.mm"
include "cn0.mm"
include "deg1nn0cl.mm"
include "syl3anc.mm"
include "nn0red.mm"
include "leidd.mm"
include "coe1mul3.mm"

theorem coe1mul4
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let cI: class I
  let cJ: class J
  assume coe1mul3.s: |- Y = ( Poly1 ` R )
  assume coe1mul3.t: |- .xb = ( .r ` Y )
  assume coe1mul3.u: |- .x. = ( .r ` R )
  assume coe1mul3.b: |- B = ( Base ` Y )
  assume coe1mul3.d: |- D = ( deg1 ` R )
  assume coe1mul4.z: |- .0. = ( 0g ` Y )
  assume coe1mul4.r: |- ( ph -> R e. Ring )
  assume coe1mul4.f1: |- ( ph -> F e. B )
  assume coe1mul4.f2: |- ( ph -> F =/= .0. )
  assume coe1mul4.g1: |- ( ph -> G e. B )
  assume coe1mul4.g2: |- ( ph -> G =/= .0. )


  assert |- ( ph -> ( ( coe1 ` ( F .xb G ) ) ` ( ( D ` F ) + ( D ` G ) ) ) = ( ( ( coe1 ` F ) ` ( D ` F ) ) .x. ( ( coe1 ` G ) ` ( D ` G ) ) ) )

  proof
    wph
    cB
    cD
    cR
    c.xb
    c.x
    cF
    cG
    cF
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    cY
    coe1mul3.s
    coe1mul3.t
    coe1mul3.u
    coe1mul3.b
    coe1mul3.d
    coe1mul4.r
    coe1mul4.f1
    wph
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    cF
    c.0
    wne
    @0
    cn0
    wcel
    coe1mul4.r
    coe1mul4.f1
    coe1mul4.f2
    cB
    cD
    cY
    cR
    cF
    c.0
    coe1mul3.d
    coe1mul3.s
    coe1mul4.z
    coe1mul3.b
    deg1nn0cl
    syl3anc
    #
    wph
    @0
    wph
    @0
    @3
    nn0red
    leidd
    coe1mul4.g1
    wph
    @2
    cG
    cB
    wcel
    cG
    c.0
    wne
    @1
    cn0
    wcel
    coe1mul4.r
    coe1mul4.g1
    coe1mul4.g2
    cB
    cD
    cY
    cR
    cG
    c.0
    coe1mul3.d
    coe1mul3.s
    coe1mul4.z
    coe1mul3.b
    deg1nn0cl
    syl3anc
    #
    wph
    @1
    wph
    @1
    @4
    nn0red
    leidd
    coe1mul3
end
