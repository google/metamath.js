include "cnx.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "setsval.mm"
include "sylancl.mm"
include "ndxid.mm"
include "strfvnd.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "uneq2d.mm"
include "wfun.mm"
include "cdm.mm"
include "funresdfunsn.mm"
include "syl2anc.mm"
include "3eqtrrd.mm"

theorem setsidvald
  let wph: wff ph
  let cS: class S
  let cE: class E
  let cN: class N
  let cV: class V
  assume setsidvald.e: |- E = Slot N
  assume setsidvald.n: |- N e. NN
  assume setsidvald.s: |- ( ph -> S e. V )
  assume setsidvald.f: |- ( ph -> Fun S )
  assume setsidvald.d: |- ( ph -> ( E ` ndx ) e. dom S )


  assert |- ( ph -> S = ( S sSet <. ( E ` ndx ) , ( E ` S ) >. ) )

  proof
    wph
    cS
    cnx
    cE
    cfv
    #
    cS
    cE
    cfv
    #
    cop
    #
    csts
    co
    #
    cS
    cvv
    @0
    csn
    cdif
    cres
    #
    @2
    csn
    #
    cun
    #
    @4
    @0
    @0
    cS
    cfv
    #
    cop
    #
    csn
    #
    cun
    #
    cS
    wph
    cS
    cV
    wcel
    @1
    cvv
    wcel
    @3
    @6
    wceq
    setsidvald.s
    cS
    cE
    fvex
    @0
    @1
    cS
    cV
    cvv
    setsval
    sylancl
    wph
    @5
    @9
    @4
    wph
    @2
    @8
    wph
    @1
    @7
    @0
    wph
    cS
    cE
    @0
    cV
    cE
    cN
    setsidvald.e
    setsidvald.n
    ndxid
    setsidvald.s
    strfvnd
    opeq2d
    sneqd
    uneq2d
    wph
    cS
    wfun
    @0
    cS
    cdm
    wcel
    @10
    cS
    wceq
    setsidvald.f
    setsidvald.d
    cS
    @0
    funresdfunsn
    syl2anc
    3eqtrrd
end
