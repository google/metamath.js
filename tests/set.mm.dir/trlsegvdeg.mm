include "ciedg.mm"
include "cfv.mm"
include "cvtx.mm"
include "eqid.mm"
include "eqtr4d.mm"
include "cdm.mm"
include "cin.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cima.mm"
include "csn.mm"
include "c0.mm"
include "trlsegvdeglem4.mm"
include "trlsegvdeglem5.mm"
include "ineq12d.mm"
include "wcel.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "fzonel.mm"
include "chash.mm"
include "wf1.mm"
include "wss.mm"
include "wb.mm"
include "ctrls.mm"
include "wbr.mm"
include "trlf1.mm"
include "syl.mm"
include "cuz.mm"
include "elfzouz2.mm"
include "fzoss2.mm"
include "3syl.mm"
include "f1elima.mm"
include "syl3anc.mm"
include "mtbiri.mm"
include "orcd.mm"
include "wa.mm"
include "ianor.mm"
include "elin.mm"
include "xchnxbir.mm"
include "sylibr.mm"
include "disjsn.mm"
include "eqtrd.mm"
include "trlsegvdeglem2.mm"
include "trlsegvdeglem3.mm"
include "eleqtrrd.mm"
include "cfz.mm"
include "cres.mm"
include "cop.mm"
include "cun.mm"
include "wf.mm"
include "f1f.mm"
include "resunimafz0.mm"
include "uneq12d.mm"
include "3eqtr4d.mm"
include "trlsegvdeglem6.mm"
include "trlsegvdeglem7.mm"
include "vtxdfiun.mm"

theorem trlsegvdeg
  let wph: wff ph
  let cP: class P
  let cU: class U
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume trlsegvdeg.v: |- V = ( Vtx ` G )
  assume trlsegvdeg.i: |- I = ( iEdg ` G )
  assume trlsegvdeg.f: |- ( ph -> Fun I )
  assume trlsegvdeg.n: |- ( ph -> N e. ( 0 ..^ ( # ` F ) ) )
  assume trlsegvdeg.u: |- ( ph -> U e. V )
  assume trlsegvdeg.w: |- ( ph -> F ( Trails ` G ) P )
  assume trlsegvdeg.vx: |- ( ph -> ( Vtx ` X ) = V )
  assume trlsegvdeg.vy: |- ( ph -> ( Vtx ` Y ) = V )
  assume trlsegvdeg.vz: |- ( ph -> ( Vtx ` Z ) = V )
  assume trlsegvdeg.ix: |- ( ph -> ( iEdg ` X ) = ( I |` ( F " ( 0 ..^ N ) ) ) )
  assume trlsegvdeg.iy: |- ( ph -> ( iEdg ` Y ) = { <. ( F ` N ) , ( I ` ( F ` N ) ) >. } )
  assume trlsegvdeg.iz: |- ( ph -> ( iEdg ` Z ) = ( I |` ( F " ( 0 ... N ) ) ) )


  assert |- ( ph -> ( ( VtxDeg ` Z ) ` U ) = ( ( ( VtxDeg ` X ) ` U ) + ( ( VtxDeg ` Y ) ` U ) ) )

  proof
    wph
    cZ
    cX
    cY
    cX
    ciedg
    cfv
    #
    cY
    ciedg
    cfv
    #
    cU
    cX
    cvtx
    cfv
    #
    @0
    eqid
    @1
    eqid
    @2
    eqid
    wph
    cY
    cvtx
    cfv
    cV
    @2
    trlsegvdeg.vy
    trlsegvdeg.vx
    eqtr4d
    wph
    cZ
    cvtx
    cfv
    cV
    @2
    trlsegvdeg.vz
    trlsegvdeg.vx
    eqtr4d
    wph
    @0
    cdm
    #
    @1
    cdm
    #
    cin
    cF
    cc0
    cN
    cfzo
    co
    #
    cima
    #
    cI
    cdm
    #
    cin
    #
    cN
    cF
    cfv
    #
    csn
    #
    cin
    #
    c0
    wph
    @3
    @8
    @4
    @10
    wph
    cP
    cU
    cF
    cG
    cI
    cN
    cV
    cX
    cY
    cZ
    trlsegvdeg.v
    trlsegvdeg.i
    trlsegvdeg.f
    trlsegvdeg.n
    trlsegvdeg.u
    trlsegvdeg.w
    trlsegvdeg.vx
    trlsegvdeg.vy
    trlsegvdeg.vz
    trlsegvdeg.ix
    trlsegvdeg.iy
    trlsegvdeg.iz
    trlsegvdeglem4
    wph
    cP
    cU
    cF
    cG
    cI
    cN
    cV
    cX
    cY
    cZ
    trlsegvdeg.v
    trlsegvdeg.i
    trlsegvdeg.f
    trlsegvdeg.n
    trlsegvdeg.u
    trlsegvdeg.w
    trlsegvdeg.vx
    trlsegvdeg.vy
    trlsegvdeg.vz
    trlsegvdeg.ix
    trlsegvdeg.iy
    trlsegvdeg.iz
    trlsegvdeglem5
    ineq12d
    wph
    @9
    @8
    wcel
    #
    wn
    #
    @11
    c0
    wceq
    wph
    @9
    @6
    wcel
    #
    wn
    #
    @9
    @7
    wcel
    #
    wn
    #
    wo
    #
    @13
    wph
    @15
    @17
    wph
    @14
    cN
    @5
    wcel
    #
    cc0
    cN
    fzonel
    wph
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    @7
    cF
    wf1
    #
    cN
    @21
    wcel
    #
    @5
    @21
    wss
    #
    @14
    @19
    wb
    wph
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    @22
    trlsegvdeg.w
    cP
    cF
    cG
    cI
    trlsegvdeg.i
    trlf1
    #
    syl
    trlsegvdeg.n
    wph
    @23
    @20
    cN
    cuz
    cfv
    wcel
    @24
    trlsegvdeg.n
    cN
    cc0
    @20
    elfzouz2
    cN
    cc0
    @20
    fzoss2
    3syl
    @21
    @7
    cF
    cN
    @5
    f1elima
    syl3anc
    mtbiri
    orcd
    @14
    @16
    wa
    @18
    @12
    @14
    @16
    ianor
    @9
    @6
    @7
    elin
    xchnxbir
    sylibr
    @8
    @9
    disjsn
    sylibr
    eqtrd
    wph
    cP
    cU
    cF
    cG
    cI
    cN
    cV
    cX
    cY
    cZ
    trlsegvdeg.v
    trlsegvdeg.i
    trlsegvdeg.f
    trlsegvdeg.n
    trlsegvdeg.u
    trlsegvdeg.w
    trlsegvdeg.vx
    trlsegvdeg.vy
    trlsegvdeg.vz
    trlsegvdeg.ix
    trlsegvdeg.iy
    trlsegvdeg.iz
    trlsegvdeglem2
    wph
    cP
    cU
    cF
    cG
    cI
    cN
    cV
    cX
    cY
    cZ
    trlsegvdeg.v
    trlsegvdeg.i
    trlsegvdeg.f
    trlsegvdeg.n
    trlsegvdeg.u
    trlsegvdeg.w
    trlsegvdeg.vx
    trlsegvdeg.vy
    trlsegvdeg.vz
    trlsegvdeg.ix
    trlsegvdeg.iy
    trlsegvdeg.iz
    trlsegvdeglem3
    wph
    cU
    cV
    @2
    trlsegvdeg.u
    trlsegvdeg.vx
    eleqtrrd
    wph
    cI
    cF
    cc0
    cN
    cfz
    co
    cima
    cres
    cI
    @6
    cres
    #
    @9
    @9
    cI
    cfv
    cop
    csn
    #
    cun
    cZ
    ciedg
    cfv
    @0
    @1
    cun
    wph
    cF
    cI
    cN
    trlsegvdeg.f
    wph
    @25
    @22
    @21
    @7
    cF
    wf
    trlsegvdeg.w
    @26
    @21
    @7
    cF
    f1f
    3syl
    trlsegvdeg.n
    resunimafz0
    trlsegvdeg.iz
    wph
    @0
    @27
    @1
    @28
    trlsegvdeg.ix
    trlsegvdeg.iy
    uneq12d
    3eqtr4d
    wph
    cP
    cU
    cF
    cG
    cI
    cN
    cV
    cX
    cY
    cZ
    trlsegvdeg.v
    trlsegvdeg.i
    trlsegvdeg.f
    trlsegvdeg.n
    trlsegvdeg.u
    trlsegvdeg.w
    trlsegvdeg.vx
    trlsegvdeg.vy
    trlsegvdeg.vz
    trlsegvdeg.ix
    trlsegvdeg.iy
    trlsegvdeg.iz
    trlsegvdeglem6
    wph
    cP
    cU
    cF
    cG
    cI
    cN
    cV
    cX
    cY
    cZ
    trlsegvdeg.v
    trlsegvdeg.i
    trlsegvdeg.f
    trlsegvdeg.n
    trlsegvdeg.u
    trlsegvdeg.w
    trlsegvdeg.vx
    trlsegvdeg.vy
    trlsegvdeg.vz
    trlsegvdeg.ix
    trlsegvdeg.iy
    trlsegvdeg.iz
    trlsegvdeglem7
    vtxdfiun
end
