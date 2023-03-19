include "csn.mm"
include "cun.mm"
include "cfv.mm"
include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "lmod0vcl.mm"
include "syl.mm"
include "snssd.mm"
include "lspun.mm"
include "syl3anc.mm"
include "lspsn0.mm"
include "uneq2d.mm"
include "clss.mm"
include "eqid.mm"
include "lspcl.mm"
include "syl2anc.mm"
include "lss0ss.mm"
include "ssequn2.mm"
include "sylib.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "lspidm.mm"

theorem lspun0
  let wph: wff ph
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lspun0.v: |- V = ( Base ` W )
  assume lspun0.o: |- .0. = ( 0g ` W )
  assume lspun0.n: |- N = ( LSpan ` W )
  assume lspun0.w: |- ( ph -> W e. LMod )
  assume lspun0.x: |- ( ph -> X C_ V )


  assert |- ( ph -> ( N ` ( X u. { .0. } ) ) = ( N ` X ) )

  proof
    wph
    cX
    c.0
    csn
    #
    cun
    cN
    cfv
    #
    cX
    cN
    cfv
    #
    @0
    cN
    cfv
    #
    cun
    #
    cN
    cfv
    #
    @2
    wph
    cW
    clmod
    wcel
    #
    cX
    cV
    wss
    #
    @0
    cV
    wss
    @1
    @5
    wceq
    lspun0.w
    lspun0.x
    wph
    c.0
    cV
    wph
    @6
    c.0
    cV
    wcel
    lspun0.w
    cV
    cW
    c.0
    lspun0.v
    lspun0.o
    lmod0vcl
    syl
    snssd
    cX
    @0
    cN
    cV
    cW
    lspun0.v
    lspun0.n
    lspun
    syl3anc
    wph
    @5
    @2
    cN
    cfv
    #
    @2
    wph
    @4
    @2
    cN
    wph
    @4
    @2
    @0
    cun
    #
    @2
    wph
    @3
    @0
    @2
    wph
    @6
    @3
    @0
    wceq
    lspun0.w
    cN
    cW
    c.0
    lspun0.o
    lspun0.n
    lspsn0
    syl
    uneq2d
    wph
    @0
    @2
    wss
    #
    @9
    @2
    wceq
    wph
    @6
    @2
    cW
    clss
    cfv
    #
    wcel
    #
    @10
    lspun0.w
    wph
    @6
    @7
    @12
    lspun0.w
    lspun0.x
    @11
    cX
    cN
    cV
    cW
    lspun0.v
    @11
    eqid
    #
    lspun0.n
    lspcl
    syl2anc
    @11
    cW
    @2
    c.0
    lspun0.o
    @13
    lss0ss
    syl2anc
    @0
    @2
    ssequn2
    sylib
    eqtrd
    fveq2d
    wph
    @6
    @7
    @8
    @2
    wceq
    lspun0.w
    lspun0.x
    cX
    cN
    cV
    cW
    lspun0.v
    lspun0.n
    lspidm
    syl2anc
    eqtrd
    eqtrd
end
