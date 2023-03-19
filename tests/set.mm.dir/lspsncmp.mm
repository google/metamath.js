include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "wa.mm"
include "clvec.mm"
include "wcel.mm"
include "adantr.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "eldifad.mm"
include "lspsnel5.mm"
include "biimpar.mm"
include "wne.mm"
include "cdif.mm"
include "eldifsni.mm"
include "lspsneleq.mm"
include "ex.mm"
include "eqimss.mm"
include "impbid1.mm"

theorem lspsncmp
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lspsncmp.v: |- V = ( Base ` W )
  assume lspsncmp.o: |- .0. = ( 0g ` W )
  assume lspsncmp.n: |- N = ( LSpan ` W )
  assume lspsncmp.w: |- ( ph -> W e. LVec )
  assume lspsncmp.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lspsncmp.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( ( N ` { X } ) C_ ( N ` { Y } ) <-> ( N ` { X } ) = ( N ` { Y } ) ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    wss
    #
    @0
    @1
    wceq
    #
    wph
    @2
    @3
    wph
    @2
    wa
    cN
    cV
    cW
    cY
    cX
    c.0
    lspsncmp.v
    lspsncmp.o
    lspsncmp.n
    wph
    cW
    clvec
    wcel
    #
    @2
    lspsncmp.w
    adantr
    wph
    cY
    cV
    wcel
    #
    @2
    lspsncmp.y
    adantr
    wph
    cX
    @1
    wcel
    @2
    wph
    cW
    clss
    cfv
    #
    @1
    cN
    cV
    cW
    cX
    lspsncmp.v
    @6
    eqid
    #
    lspsncmp.n
    wph
    @4
    cW
    clmod
    wcel
    #
    lspsncmp.w
    cW
    lveclmod
    syl
    #
    wph
    @8
    @5
    @1
    @6
    wcel
    @9
    lspsncmp.y
    @6
    cN
    cV
    cW
    cY
    lspsncmp.v
    @7
    lspsncmp.n
    lspsncl
    syl2anc
    wph
    cX
    cV
    c.0
    csn
    #
    lspsncmp.x
    eldifad
    lspsnel5
    biimpar
    wph
    cX
    c.0
    wne
    #
    @2
    wph
    cX
    cV
    @10
    cdif
    wcel
    @11
    lspsncmp.x
    cX
    cV
    c.0
    eldifsni
    syl
    adantr
    lspsneleq
    ex
    @0
    @1
    eqimss
    impbid1
end
