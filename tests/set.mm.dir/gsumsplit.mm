include "ccntz.mm"
include "cfv.mm"
include "eqid.mm"
include "ccmn.mm"
include "wcel.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "syl.mm"
include "cntzcmnf.mm"
include "gsumzsplit.mm"

theorem gsumsplit
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cV: class V
  let c.0: class .0.
  assume gsumsplit.b: |- B = ( Base ` G )
  assume gsumsplit.z: |- .0. = ( 0g ` G )
  assume gsumsplit.p: |- .+ = ( +g ` G )
  assume gsumsplit.g: |- ( ph -> G e. CMnd )
  assume gsumsplit.a: |- ( ph -> A e. V )
  assume gsumsplit.f: |- ( ph -> F : A --> B )
  assume gsumsplit.w: |- ( ph -> F finSupp .0. )
  assume gsumsplit.i: |- ( ph -> ( C i^i D ) = (/) )
  assume gsumsplit.u: |- ( ph -> A = ( C u. D ) )


  assert |- ( ph -> ( G gsum F ) = ( ( G gsum ( F |` C ) ) .+ ( G gsum ( F |` D ) ) ) )

  proof
    wph
    cA
    cB
    cC
    cD
    c.pl
    cF
    cG
    cV
    c.0
    cG
    ccntz
    cfv
    #
    gsumsplit.b
    gsumsplit.z
    gsumsplit.p
    @0
    eqid
    #
    wph
    cG
    ccmn
    wcel
    cG
    cmnd
    wcel
    gsumsplit.g
    cG
    cmnmnd
    syl
    gsumsplit.a
    gsumsplit.f
    wph
    cA
    cB
    cF
    cG
    @0
    gsumsplit.b
    @1
    gsumsplit.g
    gsumsplit.f
    cntzcmnf
    gsumsplit.w
    gsumsplit.i
    gsumsplit.u
    gsumzsplit
end
