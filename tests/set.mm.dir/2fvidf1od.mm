include "2fvcoidd.mm"
include "fcof1od.mm"

theorem 2fvidf1od
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume 2fvcoidd.f: |- ( ph -> F : A --> B )
  assume 2fvcoidd.g: |- ( ph -> G : B --> A )
  assume 2fvcoidd.i: |- ( ph -> A. a e. A ( G ` ( F ` a ) ) = a )
  assume 2fvidf1od.i: |- ( ph -> A. b e. B ( F ` ( G ` b ) ) = b )

  disjoint A a
  disjoint F a
  disjoint G a
  disjoint B b
  disjoint F b
  disjoint G b
  disjoint A x
  disjoint a x
  disjoint B x
  disjoint F x
  disjoint G x
  disjoint ph x
  assert |- ( ph -> F : A -1-1-onto-> B )

  proof
    wph
    cA
    cB
    cF
    cG
    2fvcoidd.f
    2fvcoidd.g
    wph
    cA
    cB
    cF
    cG
    va
    2fvcoidd.f
    2fvcoidd.g
    2fvcoidd.i
    2fvcoidd
    wph
    cB
    cA
    cG
    cF
    vb
    2fvcoidd.g
    2fvcoidd.f
    2fvidf1od.i
    2fvcoidd
    fcof1od
end
