include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "cn.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "ceupth.mm"
include "cwlks.mm"
include "wi.mm"
include "eupthiswlk.mm"
include "cn0.mm"
include "wlkcl.mm"
include "wa.mm"
include "cz.mm"
include "nn0z.mm"
include "anim1i.mm"
include "elnnz.mm"
include "sylibr.mm"
include "ex.mm"
include "syl.mm"
include "3syl.mm"
include "mpd.mm"
include "fzo0end.mm"
include "eqeltrd.mm"
include "eupthres.mm"

theorem eucrct2eupth1
  let wph: wff ph
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  assume eucrct2eupth1.v: |- V = ( Vtx ` G )
  assume eucrct2eupth1.i: |- I = ( iEdg ` G )
  assume eucrct2eupth1.d: |- ( ph -> F ( EulerPaths ` G ) P )
  assume eucrct2eupth1.c: |- ( ph -> F ( Circuits ` G ) P )
  assume eucrct2eupth1.s: |- ( Vtx ` S ) = V
  assume eucrct2eupth1.g: |- ( ph -> 0 < ( # ` F ) )
  assume eucrct2eupth1.n: |- ( ph -> N = ( ( # ` F ) - 1 ) )
  assume eucrct2eupth1.e: |- ( ph -> ( iEdg ` S ) = ( I |` ( F " ( 0 ..^ N ) ) ) )
  assume eucrct2eupth1.h: |- H = ( F |` ( 0 ..^ N ) )
  assume eucrct2eupth1.q: |- Q = ( P |` ( 0 ... N ) )


  assert |- ( ph -> H ( EulerPaths ` S ) Q )

  proof
    wph
    cP
    cQ
    cS
    cF
    cG
    cH
    cI
    cN
    cV
    eucrct2eupth1.v
    eucrct2eupth1.i
    eucrct2eupth1.d
    wph
    cN
    cF
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cc0
    @0
    cfzo
    co
    #
    eucrct2eupth1.n
    wph
    @0
    cn
    wcel
    #
    @1
    @2
    wcel
    wph
    cc0
    @0
    clt
    wbr
    #
    @3
    eucrct2eupth1.g
    wph
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @4
    @3
    wi
    #
    eucrct2eupth1.d
    cP
    cF
    cG
    eupthiswlk
    @5
    @0
    cn0
    wcel
    #
    @6
    cP
    cF
    cG
    wlkcl
    @7
    @4
    @3
    @7
    @4
    wa
    @0
    cz
    wcel
    #
    @4
    wa
    @3
    @7
    @8
    @4
    @0
    nn0z
    anim1i
    @0
    elnnz
    sylibr
    ex
    syl
    3syl
    mpd
    @0
    fzo0end
    syl
    eqeltrd
    eucrct2eupth1.e
    eucrct2eupth1.h
    eucrct2eupth1.q
    eucrct2eupth1.s
    eupthres
end
