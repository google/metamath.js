include "co.mm"
include "cfv.mm"
include "wbr.mm"
include "ccid.mm"
include "cop.mm"
include "cco.mm"
include "eqid.mm"
include "ciso.mm"
include "idiso.mm"
include "wceq.mm"
include "a1i.mm"
include "oveqd.mm"
include "eleqtrrd.mm"
include "invco.mm"
include "chom.mm"
include "isohom.mm"
include "sseldd.mm"
include "catlid.mm"
include "cinv.mm"
include "fveq1d.mm"
include "idinv.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "invf.mm"
include "ffvelrnd.mm"
include "catrid.mm"
include "3brtr3d.mm"
include "invsym.mm"
include "mpbird.mm"

theorem invisoinvl
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let cI: class I
  let cN: class N
  let cX: class X
  let cY: class Y
  assume invisoinv.b: |- B = ( Base ` C )
  assume invisoinv.i: |- I = ( Iso ` C )
  assume invisoinv.n: |- N = ( Inv ` C )
  assume invisoinv.c: |- ( ph -> C e. Cat )
  assume invisoinv.x: |- ( ph -> X e. B )
  assume invisoinv.y: |- ( ph -> Y e. B )
  assume invisoinv.f: |- ( ph -> F e. ( X I Y ) )


  assert |- ( ph -> ( ( X N Y ) ` F ) ( Y N X ) F )

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
    cN
    co
    wbr
    cF
    @1
    @0
    wbr
    wph
    cY
    cC
    ccid
    cfv
    #
    cfv
    #
    cF
    cX
    cY
    cop
    cY
    cC
    cco
    cfv
    #
    co
    co
    @1
    @3
    cY
    cY
    cN
    co
    #
    cfv
    #
    cY
    cY
    cop
    cX
    @4
    co
    #
    co
    #
    cF
    @1
    @0
    wph
    cB
    cC
    @4
    cF
    @3
    cI
    cN
    cX
    cY
    cY
    invisoinv.b
    invisoinv.n
    invisoinv.c
    invisoinv.x
    invisoinv.y
    invisoinv.i
    invisoinv.f
    @4
    eqid
    #
    invisoinv.y
    wph
    @3
    cY
    cY
    cC
    ciso
    cfv
    #
    co
    cY
    cY
    cI
    co
    wph
    cB
    cC
    @2
    cY
    invisoinv.b
    @2
    eqid
    #
    invisoinv.c
    invisoinv.y
    idiso
    wph
    cI
    @10
    cY
    cY
    cI
    @10
    wceq
    wph
    invisoinv.i
    a1i
    oveqd
    eleqtrrd
    invco
    wph
    cB
    cC
    @4
    @2
    cF
    cC
    chom
    cfv
    #
    cX
    cY
    invisoinv.b
    @12
    eqid
    #
    @11
    invisoinv.c
    invisoinv.x
    @9
    invisoinv.y
    wph
    cX
    cY
    cI
    co
    #
    cX
    cY
    @12
    co
    cF
    wph
    cB
    cC
    @12
    cI
    cX
    cY
    invisoinv.b
    @13
    invisoinv.i
    invisoinv.c
    invisoinv.x
    invisoinv.y
    isohom
    invisoinv.f
    sseldd
    catlid
    wph
    @8
    @1
    @3
    @7
    co
    @1
    wph
    @6
    @3
    @1
    @7
    wph
    @6
    @3
    cY
    cY
    cC
    cinv
    cfv
    #
    co
    #
    cfv
    @3
    wph
    @3
    @5
    @16
    wph
    cN
    @15
    cY
    cY
    cN
    @15
    wceq
    wph
    invisoinv.n
    a1i
    oveqd
    fveq1d
    wph
    cB
    cC
    @2
    cY
    invisoinv.b
    @11
    invisoinv.c
    invisoinv.y
    idinv
    eqtrd
    oveq2d
    wph
    cB
    cC
    @4
    @2
    @1
    @12
    cY
    cX
    invisoinv.b
    @13
    @11
    invisoinv.c
    invisoinv.y
    @9
    invisoinv.x
    wph
    cY
    cX
    cI
    co
    #
    cY
    cX
    @12
    co
    @1
    wph
    cB
    cC
    @12
    cI
    cY
    cX
    invisoinv.b
    @13
    invisoinv.i
    invisoinv.c
    invisoinv.y
    invisoinv.x
    isohom
    wph
    @14
    @17
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
    catrid
    eqtrd
    3brtr3d
    wph
    cB
    cC
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
    invsym
    mpbird
end
