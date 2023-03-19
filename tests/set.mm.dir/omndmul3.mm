include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "cmin.mm"
include "comnd.mm"
include "wcel.mm"
include "wbr.mm"
include "cmnd.mm"
include "omndmnd.mm"
include "syl.mm"
include "mndidcl.mm"
include "cn0.mm"
include "cle.mm"
include "wa.mm"
include "nn0sub.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "omndmul2.mm"
include "syl121anc.mm"
include "eqid.mm"
include "omndadd.mm"
include "syl131anc.mm"
include "wceq.mm"
include "mndlid.mm"
include "syl2anc.mm"
include "caddc.mm"
include "mulgnn0dir.mm"
include "syl13anc.mm"
include "nn0cnd.mm"
include "npcand.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "3brtr3d.mm"

theorem omndmul3
  let wph: wff ph
  let cB: class B
  let cP: class P
  let c.x: class .x.
  let c.le: class .<_
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vm: setvar m
  let vn: setvar n
  let cY: class Y
  assume omndmul.0: |- B = ( Base ` M )
  assume omndmul.1: |- .<_ = ( le ` M )
  assume omndmul3.m: |- .x. = ( .g ` M )
  assume omndmul3.0: |- .0. = ( 0g ` M )
  assume omndmul3.o: |- ( ph -> M e. oMnd )
  assume omndmul3.1: |- ( ph -> N e. NN0 )
  assume omndmul3.2: |- ( ph -> P e. NN0 )
  assume omndmul3.3: |- ( ph -> N <_ P )
  assume omndmul3.4: |- ( ph -> X e. B )
  assume omndmul3.5: |- ( ph -> .0. .<_ X )


  assert |- ( ph -> ( N .x. X ) .<_ ( P .x. X ) )

  proof
    wph
    c.0
    cN
    cX
    c.x
    co
    #
    cM
    cplusg
    cfv
    #
    co
    #
    cP
    cN
    cmin
    co
    #
    cX
    c.x
    co
    #
    @0
    @1
    co
    #
    @0
    cP
    cX
    c.x
    co
    #
    c.le
    wph
    cM
    comnd
    wcel
    #
    c.0
    cB
    wcel
    #
    @4
    cB
    wcel
    #
    @0
    cB
    wcel
    #
    c.0
    @4
    c.le
    wbr
    #
    @2
    @5
    c.le
    wbr
    omndmul3.o
    wph
    cM
    cmnd
    wcel
    #
    @8
    wph
    @7
    @12
    omndmul3.o
    cM
    omndmnd
    syl
    #
    cB
    cM
    c.0
    omndmul.0
    omndmul3.0
    mndidcl
    syl
    wph
    @12
    @3
    cn0
    wcel
    #
    cX
    cB
    wcel
    #
    @9
    @13
    wph
    cN
    cn0
    wcel
    #
    cP
    cn0
    wcel
    #
    cN
    cP
    cle
    wbr
    #
    @14
    omndmul3.1
    omndmul3.2
    omndmul3.3
    @16
    @17
    wa
    @18
    @14
    cN
    cP
    nn0sub
    biimpa
    syl21anc
    #
    omndmul3.4
    cB
    c.x
    cM
    @3
    cX
    omndmul.0
    omndmul3.m
    mulgnn0cl
    syl3anc
    wph
    @12
    @16
    @15
    @10
    @13
    omndmul3.1
    omndmul3.4
    cB
    c.x
    cM
    cN
    cX
    omndmul.0
    omndmul3.m
    mulgnn0cl
    syl3anc
    #
    wph
    @7
    @15
    @14
    c.0
    cX
    c.le
    wbr
    @11
    omndmul3.o
    omndmul3.4
    @19
    omndmul3.5
    cB
    c.x
    c.le
    cM
    @3
    cX
    c.0
    omndmul.0
    omndmul.1
    omndmul3.m
    omndmul3.0
    omndmul2
    syl121anc
    cB
    @1
    c.le
    cM
    c.0
    @4
    @0
    omndmul.0
    omndmul.1
    @1
    eqid
    #
    omndadd
    syl131anc
    wph
    @12
    @10
    @2
    @0
    wceq
    @13
    @20
    cB
    @1
    cM
    @0
    c.0
    omndmul.0
    @21
    omndmul3.0
    mndlid
    syl2anc
    wph
    @3
    cN
    caddc
    co
    #
    cX
    c.x
    co
    #
    @5
    @6
    wph
    @12
    @14
    @16
    @15
    @23
    @5
    wceq
    @13
    @19
    omndmul3.1
    omndmul3.4
    cB
    @1
    c.x
    cM
    @3
    cN
    cX
    omndmul.0
    omndmul3.m
    @21
    mulgnn0dir
    syl13anc
    wph
    @22
    cP
    cX
    c.x
    wph
    cP
    cN
    wph
    cP
    omndmul3.2
    nn0cnd
    wph
    cN
    omndmul3.1
    nn0cnd
    npcand
    oveq1d
    eqtr3d
    3brtr3d
end
