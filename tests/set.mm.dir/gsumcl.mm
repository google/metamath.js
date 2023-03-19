include "fsuppimpd.mm"
include "gsumcl2.mm"

theorem gsumcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let c.0: class .0.
  assume gsumcl.b: |- B = ( Base ` G )
  assume gsumcl.z: |- .0. = ( 0g ` G )
  assume gsumcl.g: |- ( ph -> G e. CMnd )
  assume gsumcl.a: |- ( ph -> A e. V )
  assume gsumcl.f: |- ( ph -> F : A --> B )
  assume gsumcl.w: |- ( ph -> F finSupp .0. )


  assert |- ( ph -> ( G gsum F ) e. B )

  proof
    wph
    cA
    cB
    cF
    cG
    cV
    c.0
    gsumcl.b
    gsumcl.z
    gsumcl.g
    gsumcl.a
    gsumcl.f
    wph
    cF
    c.0
    gsumcl.w
    fsuppimpd
    gsumcl2
end
