include "ccntz.mm"
include "cfv.mm"
include "eqid.mm"
include "ccmn.mm"
include "wcel.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "syl.mm"
include "csubmnd.mm"
include "submid.mm"
include "ssid.mm"
include "wss.mm"
include "wceq.mm"
include "cntzcmn.mm"
include "sylancl.mm"
include "syl5sseqr.mm"
include "gsumzadd.mm"

theorem gsumadd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let c.0: class .0.
  assume gsumadd.b: |- B = ( Base ` G )
  assume gsumadd.z: |- .0. = ( 0g ` G )
  assume gsumadd.p: |- .+ = ( +g ` G )
  assume gsumadd.g: |- ( ph -> G e. CMnd )
  assume gsumadd.a: |- ( ph -> A e. V )
  assume gsumadd.f: |- ( ph -> F : A --> B )
  assume gsumadd.h: |- ( ph -> H : A --> B )
  assume gsumadd.fn: |- ( ph -> F finSupp .0. )
  assume gsumadd.hn: |- ( ph -> H finSupp .0. )


  assert |- ( ph -> ( G gsum ( F oF .+ H ) ) = ( ( G gsum F ) .+ ( G gsum H ) ) )

  proof
    wph
    cA
    cB
    c.pl
    cB
    cF
    cG
    cH
    cV
    c.0
    cG
    ccntz
    cfv
    #
    gsumadd.b
    gsumadd.z
    gsumadd.p
    @0
    eqid
    #
    wph
    cG
    ccmn
    wcel
    #
    cG
    cmnd
    wcel
    #
    gsumadd.g
    cG
    cmnmnd
    syl
    #
    gsumadd.a
    gsumadd.fn
    gsumadd.hn
    wph
    @3
    cB
    cG
    csubmnd
    cfv
    wcel
    @4
    cB
    cG
    gsumadd.b
    submid
    syl
    wph
    cB
    cB
    cB
    @0
    cfv
    #
    cB
    ssid
    #
    wph
    @2
    cB
    cB
    wss
    @5
    cB
    wceq
    gsumadd.g
    @6
    cB
    cB
    cG
    @0
    gsumadd.b
    @1
    cntzcmn
    sylancl
    syl5sseqr
    gsumadd.f
    gsumadd.h
    gsumzadd
end
