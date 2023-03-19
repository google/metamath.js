include "c2nd.mm"
include "cfv.mm"
include "co.mm"
include "cid.mm"
include "cres.mm"
include "idfu2nd.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "fvresi.mm"
include "syl.mm"
include "eqtrd.mm"

theorem idfu2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let cH: class H
  let cI: class I
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vc: setvar c
  let vz: setvar z
  assume idfuval.i: |- I = ( idFunc ` C )
  assume idfuval.b: |- B = ( Base ` C )
  assume idfuval.c: |- ( ph -> C e. Cat )
  assume idfuval.h: |- H = ( Hom ` C )
  assume idfu2nd.x: |- ( ph -> X e. B )
  assume idfu2nd.y: |- ( ph -> Y e. B )
  assume idfu2.f: |- ( ph -> F e. ( X H Y ) )


  assert |- ( ph -> ( ( X ( 2nd ` I ) Y ) ` F ) = F )

  proof
    wph
    cF
    cX
    cY
    cI
    c2nd
    cfv
    co
    #
    cfv
    cF
    cid
    cX
    cY
    cH
    co
    #
    cres
    #
    cfv
    #
    cF
    wph
    cF
    @0
    @2
    wph
    cB
    cC
    cH
    cI
    cX
    cY
    idfuval.i
    idfuval.b
    idfuval.c
    idfuval.h
    idfu2nd.x
    idfu2nd.y
    idfu2nd
    fveq1d
    wph
    cF
    @1
    wcel
    @3
    cF
    wceq
    idfu2.f
    @1
    cF
    fvresi
    syl
    eqtrd
end
