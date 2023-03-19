include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cin.mm"
include "eqid.mm"
include "ressbas.mm"
include "inss2.mm"
include "syl6eqssr.mm"

theorem lidlssbas
  let cR: class R
  let cU: class U
  let cI: class I
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x
  assume lidlabl.l: |- L = ( LIdeal ` R )
  assume lidlabl.i: |- I = ( R |`s U )


  assert |- ( U e. L -> ( Base ` I ) C_ ( Base ` R ) )

  proof
    cU
    cL
    wcel
    cI
    cbs
    cfv
    cU
    cR
    cbs
    cfv
    #
    cin
    @0
    cU
    @0
    cI
    cL
    cR
    lidlabl.i
    @0
    eqid
    ressbas
    cU
    @0
    inss2
    syl6eqssr
end
