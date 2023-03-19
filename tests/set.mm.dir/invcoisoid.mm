include "co.mm"
include "cfv.mm"
include "csect.mm"
include "wbr.mm"
include "wceq.mm"
include "invisoinvr.mm"
include "wa.mm"
include "eqid.mm"
include "isinv.mm"
include "simpl.mm"
include "syl6bi.mm"
include "mpd.mm"
include "cop.mm"
include "cco.mm"
include "chom.mm"
include "isohom.mm"
include "sseldd.mm"
include "invf.mm"
include "ffvelrnd.mm"
include "issect2.mm"
include "a1i.mm"
include "eqcomd.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "mpbid.mm"

theorem invcoisoid
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.1: class .1.
  let cF: class F
  let cI: class I
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.op: class .o.
  assume invisoinv.b: |- B = ( Base ` C )
  assume invisoinv.i: |- I = ( Iso ` C )
  assume invisoinv.n: |- N = ( Inv ` C )
  assume invisoinv.c: |- ( ph -> C e. Cat )
  assume invisoinv.x: |- ( ph -> X e. B )
  assume invisoinv.y: |- ( ph -> Y e. B )
  assume invisoinv.f: |- ( ph -> F e. ( X I Y ) )
  assume invcoisoid.1: |- .1. = ( Id ` C )
  assume invcoisoid.o: |- .o. = ( <. X , Y >. ( comp ` C ) X )


  assert |- ( ph -> ( ( ( X N Y ) ` F ) .o. F ) = ( .1. ` X ) )

  proof
    wph
    cF
    cF
    cX
    cY
    cN
    co
    #
    cfv
    #
    cX
    cY
    cC
    csect
    cfv
    #
    co
    wbr
    #
    @1
    cF
    c.op
    co
    #
    cX
    c.1
    cfv
    #
    wceq
    #
    wph
    cF
    @1
    @0
    wbr
    #
    @3
    wph
    cB
    cC
    cF
    cI
    cN
    cX
    cY
    invisoinv.b
    invisoinv.i
    invisoinv.n
    invisoinv.c
    invisoinv.x
    invisoinv.y
    invisoinv.f
    invisoinvr
    wph
    @7
    @3
    @1
    cF
    cY
    cX
    @2
    co
    wbr
    #
    wa
    @3
    wph
    cB
    cC
    @2
    cF
    @1
    cN
    cX
    cY
    invisoinv.b
    invisoinv.n
    invisoinv.c
    invisoinv.x
    invisoinv.y
    @2
    eqid
    #
    isinv
    @3
    @8
    simpl
    syl6bi
    mpd
    wph
    @3
    @1
    cF
    cX
    cY
    cop
    cX
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    @5
    wceq
    @6
    wph
    cB
    cC
    @2
    @10
    c.1
    cF
    @1
    cC
    chom
    cfv
    #
    cX
    cY
    invisoinv.b
    @13
    eqid
    #
    @10
    eqid
    invcoisoid.1
    @9
    invisoinv.c
    invisoinv.x
    invisoinv.y
    wph
    cX
    cY
    cI
    co
    #
    cX
    cY
    @13
    co
    cF
    wph
    cB
    cC
    @13
    cI
    cX
    cY
    invisoinv.b
    @14
    invisoinv.i
    invisoinv.c
    invisoinv.x
    invisoinv.y
    isohom
    invisoinv.f
    sseldd
    wph
    cY
    cX
    cI
    co
    #
    cY
    cX
    @13
    co
    @1
    wph
    cB
    cC
    @13
    cI
    cY
    cX
    invisoinv.b
    @14
    invisoinv.i
    invisoinv.c
    invisoinv.y
    invisoinv.x
    isohom
    wph
    @15
    @16
    cF
    @0
    wph
    cB
    cC
    cI
    cN
    cX
    cY
    invisoinv.b
    invisoinv.n
    invisoinv.c
    invisoinv.x
    invisoinv.y
    invisoinv.i
    invf
    invisoinv.f
    ffvelrnd
    sseldd
    issect2
    wph
    @12
    @4
    @5
    wph
    @11
    c.op
    @1
    cF
    wph
    c.op
    @11
    c.op
    @11
    wceq
    wph
    invcoisoid.o
    a1i
    eqcomd
    oveqd
    eqeq1d
    bitrd
    mpbid
end
