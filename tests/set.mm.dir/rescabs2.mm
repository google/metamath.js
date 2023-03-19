include "cress.mm"
include "co.mm"
include "cnx.mm"
include "chom.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "cresc.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "ressabs.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "cvv.mm"
include "eqid.mm"
include "ovexd.mm"
include "ssexd.mm"
include "rescval2.mm"
include "3eqtr4d.mm"

theorem rescabs2
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cT: class T
  let cJ: class J
  let cV: class V
  let cW: class W
  assume rescabs2.c: |- ( ph -> C e. V )
  assume rescabs2.j: |- ( ph -> J Fn ( T X. T ) )
  assume rescabs2.s: |- ( ph -> S e. W )
  assume rescabs2.t: |- ( ph -> T C_ S )


  assert |- ( ph -> ( ( C |`s S ) |`cat J ) = ( C |`cat J ) )

  proof
    wph
    cC
    cS
    cress
    co
    #
    cT
    cress
    co
    #
    cnx
    chom
    cfv
    cJ
    cop
    #
    csts
    co
    cC
    cT
    cress
    co
    #
    @2
    csts
    co
    @0
    cJ
    cresc
    co
    #
    cC
    cJ
    cresc
    co
    #
    wph
    @1
    @3
    @2
    csts
    wph
    cS
    cW
    wcel
    cT
    cS
    wss
    @1
    @3
    wceq
    rescabs2.s
    rescabs2.t
    cS
    cT
    cC
    cW
    ressabs
    syl2anc
    oveq1d
    wph
    @0
    @4
    cT
    cJ
    cvv
    cvv
    @4
    eqid
    wph
    cC
    cS
    cress
    ovexd
    wph
    cT
    cS
    cW
    rescabs2.s
    rescabs2.t
    ssexd
    #
    rescabs2.j
    rescval2
    wph
    cC
    @5
    cT
    cJ
    cV
    cvv
    @5
    eqid
    rescabs2.c
    @6
    rescabs2.j
    rescval2
    3eqtr4d
end
