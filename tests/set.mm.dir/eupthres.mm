include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cima.mm"
include "cres.mm"
include "cdm.mm"
include "wf1o.mm"
include "ctrls.mm"
include "eupthistrl.mm"
include "trliswlk.mm"
include "3syl.mm"
include "cvtx.mm"
include "wceq.mm"
include "a1i.mm"
include "wlkres.mm"
include "syl.mm"
include "trlreslem.mm"
include "ciedg.mm"
include "wa.mm"
include "eqid.mm"
include "iseupthf1o.mm"
include "dmeqd.mm"
include "f1oeq3d.mm"
include "anbi2d.mm"
include "syl5bb.mm"
include "mpbir2and.mm"

theorem eupthres
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
  assume eupth0.v: |- V = ( Vtx ` G )
  assume eupth0.i: |- I = ( iEdg ` G )
  assume eupthres.d: |- ( ph -> F ( EulerPaths ` G ) P )
  assume eupthres.n: |- ( ph -> N e. ( 0 ..^ ( # ` F ) ) )
  assume eupthres.e: |- ( ph -> ( iEdg ` S ) = ( I |` ( F " ( 0 ..^ N ) ) ) )
  assume eupthres.h: |- H = ( F |` ( 0 ..^ N ) )
  assume eupthres.q: |- Q = ( P |` ( 0 ... N ) )
  assume eupthres.s: |- ( Vtx ` S ) = V


  assert |- ( ph -> H ( EulerPaths ` S ) Q )

  proof
    wph
    cH
    cQ
    cS
    ceupth
    cfv
    wbr
    #
    cH
    cQ
    cS
    cwlks
    cfv
    wbr
    #
    cc0
    cH
    chash
    cfv
    cfzo
    co
    #
    cI
    cF
    cc0
    cN
    cfzo
    co
    cima
    cres
    #
    cdm
    #
    cH
    wf1o
    #
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
    eupth0.v
    eupth0.i
    wph
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    #
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    eupthres.d
    cP
    cF
    cG
    eupthistrl
    #
    cP
    cF
    cG
    trliswlk
    3syl
    eupthres.n
    cS
    cvtx
    cfv
    cV
    wceq
    wph
    eupthres.s
    a1i
    eupthres.e
    eupthres.h
    eupthres.q
    wlkres
    wph
    cP
    cF
    cG
    cH
    cI
    cN
    cV
    eupth0.v
    eupth0.i
    wph
    @6
    @7
    eupthres.d
    @8
    syl
    eupthres.n
    eupthres.h
    trlreslem
    @0
    @1
    @2
    cS
    ciedg
    cfv
    #
    cdm
    #
    cH
    wf1o
    #
    wa
    wph
    @1
    @5
    wa
    cQ
    cH
    cS
    @9
    @9
    eqid
    iseupthf1o
    wph
    @11
    @5
    @1
    wph
    @10
    @4
    @2
    cH
    wph
    @9
    @3
    eupthres.e
    dmeqd
    f1oeq3d
    anbi2d
    syl5bb
    mpbir2and
end
