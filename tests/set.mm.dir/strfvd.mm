include "cfv.mm"
include "cnx.mm"
include "strfvnd.mm"
include "wfun.mm"
include "cop.mm"
include "wcel.mm"
include "wceq.mm"
include "funopfv.mm"
include "sylc.mm"
include "eqtr2d.mm"

theorem strfvd
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cE: class E
  let cV: class V
  assume strfvd.e: |- E = Slot ( E ` ndx )
  assume strfvd.s: |- ( ph -> S e. V )
  assume strfvd.f: |- ( ph -> Fun S )
  assume strfvd.n: |- ( ph -> <. ( E ` ndx ) , C >. e. S )


  assert |- ( ph -> C = ( E ` S ) )

  proof
    wph
    cS
    cE
    cfv
    cnx
    cE
    cfv
    #
    cS
    cfv
    #
    cC
    wph
    cS
    cE
    @0
    cV
    strfvd.e
    strfvd.s
    strfvnd
    wph
    cS
    wfun
    @0
    cC
    cop
    cS
    wcel
    @1
    cC
    wceq
    strfvd.f
    strfvd.n
    @0
    cC
    cS
    funopfv
    sylc
    eqtr2d
end
