include "fsuppimpd.mm"
include "gsumzcl2.mm"

theorem gsumzcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  let cH: class H
  let cC: class C
  let cW: class W
  assume gsumzcl.b: |- B = ( Base ` G )
  assume gsumzcl.0: |- .0. = ( 0g ` G )
  assume gsumzcl.z: |- Z = ( Cntz ` G )
  assume gsumzcl.g: |- ( ph -> G e. Mnd )
  assume gsumzcl.a: |- ( ph -> A e. V )
  assume gsumzcl.f: |- ( ph -> F : A --> B )
  assume gsumzcl.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumzcl.w: |- ( ph -> F finSupp .0. )


  assert |- ( ph -> ( G gsum F ) e. B )

  proof
    wph
    cA
    cB
    cF
    cG
    cV
    c.0
    cZ
    gsumzcl.b
    gsumzcl.0
    gsumzcl.z
    gsumzcl.g
    gsumzcl.a
    gsumzcl.f
    gsumzcl.c
    wph
    cF
    c.0
    gsumzcl.w
    fsuppimpd
    gsumzcl2
end
