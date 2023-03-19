include "co.mm"
include "cfv.mm"
include "csect.mm"
include "wbr.mm"
include "wceq.mm"
include "invisoinvl.mm"
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
include "invf.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "issect2.mm"
include "a1i.mm"
include "eqcomd.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "mpbid.mm"

theorem isocoinvid
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
  assume isocoinvid.o: |- .o. = ( <. Y , X >. ( comp ` C ) Y )


  assert |- ( ph -> ( F .o. ( ( X N Y ) ` F ) ) = ( .1. ` Y ) )

  proof
    wph
    cF
    cX
    cY
    cN
    co
    #
    cfv
    #
    cF
    cY
    cX
    cC
    csect
    cfv
    #
    co
    wbr
    #
    cF
    @1
    c.op
    co
    #
    cY
    c.1
    cfv
    #
    wceq
    #
    wph
    @1
    cF
    cY
    cX
    cN
    co
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
    invisoinvl
    wph
    @7
    @3
    cF
    @1
    cX
    cY
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
    @1
    cF
    cN
    cY
    cX
    invisoinv.b
    invisoinv.n
    invisoinv.c
    invisoinv.y
    invisoinv.x
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
    cF
    @1
    cY
    cX
    cop
    cY
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
    @1
    cF
    cC
    chom
    cfv
    #
    cY
    cX
    invisoinv.b
    @13
    eqid
    #
    @10
    eqid
    invcoisoid.1
    @9
    invisoinv.c
    invisoinv.y
    invisoinv.x
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
    cX
    cY
    cI
    co
    #
    @15
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
    wph
    @16
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
    issect2
    wph
    @12
    @4
    @5
    wph
    @11
    c.op
    cF
    @1
    wph
    c.op
    @11
    c.op
    @11
    wceq
    wph
    isocoinvid.o
    a1i
    eqcomd
    oveqd
    eqeq1d
    bitrd
    mpbid
end
