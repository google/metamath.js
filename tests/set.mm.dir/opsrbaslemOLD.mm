include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cnx.mm"
include "cple.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "cxp.mm"
include "wss.mm"
include "adantr.mm"
include "opsrval2.mm"
include "fveq2d.mm"
include "ndxid.mm"
include "wne.mm"
include "c10.mm"
include "nnrei.mm"
include "ltneii.mm"
include "ndxarg.mm"
include "plendxOLD.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "syl6reqr.mm"
include "wn.mm"
include "cmps.mm"
include "copws.mm"
include "c0.mm"
include "0fv.mm"
include "eqcomi.mm"
include "reldmpsr.mm"
include "ovprc.mm"
include "reldmopsr.mm"
include "fveq1d.mm"
include "3eqtr4a.mm"
include "adantl.mm"
include "3eqtr4g.mm"
include "pm2.61dan.mm"

theorem opsrbaslemOLD
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let cE: class E
  let cI: class I
  let cN: class N
  let cO: class O
  assume opsrbas.s: |- S = ( I mPwSer R )
  assume opsrbas.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrbas.t: |- ( ph -> T C_ ( I X. I ) )
  assume opsrbaslemOLD.1: |- E = Slot N
  assume opsrbaslemOLD.2: |- N e. NN
  assume opsrbaslemOLD.3: |- N < 10


  assert |- ( ph -> ( E ` S ) = ( E ` O ) )

  proof
    wph
    cI
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    #
    cS
    cE
    cfv
    #
    cO
    cE
    cfv
    #
    wceq
    wph
    @2
    wa
    #
    @4
    cS
    cnx
    cple
    cfv
    #
    cO
    cple
    cfv
    #
    cop
    csts
    co
    #
    cE
    cfv
    @3
    @5
    cO
    @8
    cE
    @5
    cR
    cS
    cT
    cI
    @7
    cO
    cvv
    cvv
    opsrbas.s
    opsrbas.o
    @7
    eqid
    wph
    @0
    @1
    simprl
    wph
    @0
    @1
    simprr
    wph
    cT
    cI
    cI
    cxp
    wss
    @2
    opsrbas.t
    adantr
    opsrval2
    fveq2d
    @7
    @6
    cE
    cS
    cE
    cN
    opsrbaslemOLD.1
    opsrbaslemOLD.2
    ndxid
    cnx
    cE
    cfv
    #
    @6
    wne
    cN
    c10
    wne
    cN
    c10
    cN
    opsrbaslemOLD.2
    nnrei
    opsrbaslemOLD.3
    ltneii
    @9
    cN
    @6
    c10
    cE
    cN
    opsrbaslemOLD.1
    opsrbaslemOLD.2
    ndxarg
    plendxOLD
    neeq12i
    mpbir
    setsnid
    syl6reqr
    wph
    @2
    wn
    #
    wa
    #
    cS
    cO
    cE
    @11
    cI
    cR
    cmps
    co
    #
    cT
    cI
    cR
    copws
    co
    #
    cfv
    #
    cS
    cO
    @10
    @12
    @14
    wceq
    wph
    @10
    c0
    cT
    c0
    cfv
    #
    @12
    @14
    @15
    c0
    cT
    0fv
    eqcomi
    cI
    cR
    cmps
    reldmpsr
    ovprc
    @10
    cT
    @13
    c0
    cI
    cR
    copws
    reldmopsr
    ovprc
    fveq1d
    3eqtr4a
    adantl
    opsrbas.s
    opsrbas.o
    3eqtr4g
    fveq2d
    pm2.61dan
end
