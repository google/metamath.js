include "cn0.mm"
include "wcel.mm"
include "cfv.mm"
include "cnx.mm"
include "cple.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "eqid.mm"
include "znval2.mm"
include "fveq2d.mm"
include "ndxid.mm"
include "wne.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "nnrei.mm"
include "ltneii.mm"
include "ndxarg.mm"
include "plendx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "syl6reqr.mm"

theorem znbaslem
  let cS: class S
  let cU: class U
  let cE: class E
  let cK: class K
  let cN: class N
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume znval2.s: |- S = ( RSpan ` ZZring )
  assume znval2.u: |- U = ( ZZring /s ( ZZring ~QG ( S ` { N } ) ) )
  assume znval2.y: |- Y = ( Z/nZ ` N )
  assume znbaslem.e: |- E = Slot K
  assume znbaslem.k: |- K e. NN
  assume znbaslem.l: |- K < ; 1 0


  assert |- ( N e. NN0 -> ( E ` U ) = ( E ` Y ) )

  proof
    cN
    cn0
    wcel
    #
    cY
    cE
    cfv
    cU
    cnx
    cple
    cfv
    #
    cY
    cple
    cfv
    #
    cop
    csts
    co
    #
    cE
    cfv
    cU
    cE
    cfv
    @0
    cY
    @3
    cE
    cS
    cU
    @2
    cN
    cY
    znval2.s
    znval2.u
    znval2.y
    @2
    eqid
    znval2
    fveq2d
    @2
    @1
    cE
    cU
    cE
    cK
    znbaslem.e
    znbaslem.k
    ndxid
    cnx
    cE
    cfv
    #
    @1
    wne
    cK
    c1
    cc0
    cdc
    #
    wne
    cK
    @5
    cK
    znbaslem.k
    nnrei
    znbaslem.l
    ltneii
    @4
    cK
    @1
    @5
    cE
    cK
    znbaslem.e
    znbaslem.k
    ndxarg
    plendx
    neeq12i
    mpbir
    setsnid
    syl6reqr
end
