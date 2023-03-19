include "wcel.mm"
include "wn.mm"
include "csn.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "clvec.mm"
include "adantr.mm"
include "eldifad.mm"
include "simpr.mm"
include "lspdisj.mm"
include "wne.mm"
include "cdif.mm"
include "eldifsni.mm"
include "syl.mm"
include "wi.mm"
include "clmod.mm"
include "lveclmod.mm"
include "lspsnid.mm"
include "syl2anc.mm"
include "elin.mm"
include "eleq2.mm"
include "elsni.mm"
include "syl6bi.mm"
include "syl5bir.mm"
include "expd.mm"
include "mpan9.mm"
include "necon3ad.mm"
include "mpd.mm"
include "impbida.mm"

theorem lspdisjb
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lspdisjb.v: |- V = ( Base ` W )
  assume lspdisjb.o: |- .0. = ( 0g ` W )
  assume lspdisjb.n: |- N = ( LSpan ` W )
  assume lspdisjb.s: |- S = ( LSubSp ` W )
  assume lspdisjb.w: |- ( ph -> W e. LVec )
  assume lspdisjb.u: |- ( ph -> U e. S )
  assume lspdisjb.x: |- ( ph -> X e. ( V \ { .0. } ) )


  assert |- ( ph -> ( -. X e. U <-> ( ( N ` { X } ) i^i U ) = { .0. } ) )

  proof
    wph
    cX
    cU
    wcel
    #
    wn
    #
    cX
    csn
    cN
    cfv
    #
    cU
    cin
    #
    c.0
    csn
    #
    wceq
    #
    wph
    @1
    wa
    cS
    cU
    cN
    cV
    cW
    cX
    c.0
    lspdisjb.v
    lspdisjb.o
    lspdisjb.n
    lspdisjb.s
    wph
    cW
    clvec
    wcel
    #
    @1
    lspdisjb.w
    adantr
    wph
    cU
    cS
    wcel
    @1
    lspdisjb.u
    adantr
    wph
    cX
    cV
    wcel
    #
    @1
    wph
    cX
    cV
    @4
    lspdisjb.x
    eldifad
    #
    adantr
    wph
    @1
    simpr
    lspdisj
    wph
    @5
    wa
    #
    cX
    c.0
    wne
    #
    @1
    wph
    @10
    @5
    wph
    cX
    cV
    @4
    cdif
    wcel
    @10
    lspdisjb.x
    cX
    cV
    c.0
    eldifsni
    syl
    adantr
    @9
    @0
    cX
    c.0
    wph
    cX
    @2
    wcel
    #
    @5
    @0
    cX
    c.0
    wceq
    #
    wi
    wph
    cW
    clmod
    wcel
    #
    @7
    @11
    wph
    @6
    @13
    lspdisjb.w
    cW
    lveclmod
    syl
    @8
    cN
    cV
    cW
    cX
    lspdisjb.v
    lspdisjb.n
    lspsnid
    syl2anc
    @5
    @11
    @0
    @12
    @11
    @0
    wa
    cX
    @3
    wcel
    #
    @5
    @12
    cX
    @2
    cU
    elin
    @5
    @14
    cX
    @4
    wcel
    @12
    @3
    @4
    cX
    eleq2
    cX
    c.0
    elsni
    syl6bi
    syl5bir
    expd
    mpan9
    necon3ad
    mpd
    impbida
end
