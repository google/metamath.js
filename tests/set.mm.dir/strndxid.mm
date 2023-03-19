include "cfv.mm"
include "cnx.mm"
include "ndxid.mm"
include "strfvnd.mm"
include "eqcomd.mm"

theorem strndxid
  let wph: wff ph
  let cS: class S
  let cE: class E
  let cN: class N
  let cV: class V
  assume strndxid.s: |- ( ph -> S e. V )
  assume strndxid.e: |- E = Slot N
  assume strndxid.n: |- N e. NN


  assert |- ( ph -> ( S ` ( E ` ndx ) ) = ( E ` S ) )

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
    wph
    cS
    cE
    @0
    cV
    cE
    cN
    strndxid.e
    strndxid.n
    ndxid
    strndxid.s
    strfvnd
    eqcomd
end
