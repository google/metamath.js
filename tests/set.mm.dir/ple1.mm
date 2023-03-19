include "cfv.mm"
include "luble.mm"
include "wcel.mm"
include "wceq.mm"
include "p1val.mm"
include "syl.mm"
include "breqtrrd.mm"

theorem ple1
  let wph: wff ph
  let cB: class B
  let cU: class U
  let c.1: class .1.
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  assume ple1.b: |- B = ( Base ` K )
  assume ple1.u: |- U = ( lub ` K )
  assume ple1.l: |- .<_ = ( le ` K )
  assume ple1.1: |- .1. = ( 1. ` K )
  assume ple1.k: |- ( ph -> K e. V )
  assume ple1.x: |- ( ph -> X e. B )
  assume ple1.d: |- ( ph -> B e. dom U )


  assert |- ( ph -> X .<_ .1. )

  proof
    wph
    cX
    cB
    cU
    cfv
    #
    c.1
    c.le
    wph
    cB
    cB
    cU
    cK
    c.le
    cV
    cX
    ple1.b
    ple1.l
    ple1.u
    ple1.k
    ple1.d
    ple1.x
    luble
    wph
    cK
    cV
    wcel
    c.1
    @0
    wceq
    ple1.k
    cB
    cU
    c.1
    cK
    cV
    ple1.b
    ple1.u
    ple1.1
    p1val
    syl
    breqtrrd
end
