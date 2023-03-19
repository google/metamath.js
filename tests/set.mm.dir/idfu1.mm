include "c1st.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "idfu1st.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "fvresi.mm"
include "syl.mm"
include "eqtrd.mm"

theorem idfu1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cI: class I
  let cX: class X
  let vb: setvar b
  let vc: setvar c
  let vz: setvar z
  let cH: class H
  let cY: class Y
  assume idfuval.i: |- I = ( idFunc ` C )
  assume idfuval.b: |- B = ( Base ` C )
  assume idfuval.c: |- ( ph -> C e. Cat )
  assume idfu1.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( ( 1st ` I ) ` X ) = X )

  proof
    wph
    cX
    cI
    c1st
    cfv
    #
    cfv
    cX
    cid
    cB
    cres
    #
    cfv
    #
    cX
    wph
    cX
    @0
    @1
    wph
    cB
    cC
    cI
    idfuval.i
    idfuval.b
    idfuval.c
    idfu1st
    fveq1d
    wph
    cX
    cB
    wcel
    @2
    cX
    wceq
    idfu1.x
    cB
    cX
    fvresi
    syl
    eqtrd
end
