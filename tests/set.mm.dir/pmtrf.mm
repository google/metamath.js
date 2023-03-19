include "wcel.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cif.mm"
include "cmpt.mm"
include "wa.mm"
include "simpll2.mm"
include "c1o.mm"
include "com.mm"
include "csuc.mm"
include "1onn.mm"
include "a1i.mm"
include "simpll3.mm"
include "df-2o.mm"
include "syl6breq.mm"
include "simpr.mm"
include "dif1en.mm"
include "syl3anc.mm"
include "en1uniel.mm"
include "eldifi.mm"
include "3syl.mm"
include "sseldd.mm"
include "wn.mm"
include "simplr.mm"
include "ifclda.mm"
include "eqid.mm"
include "fmptd.mm"
include "pmtrval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem pmtrf
  let cD: class D
  let cP: class P
  let cT: class T
  let cV: class V
  let vd: setvar d
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let cZ: class Z
  assume pmtrfval.t: |- T = ( pmTrsp ` D )


  assert |- ( ( D e. V /\ P C_ D /\ P ~~ 2o ) -> ( T ` P ) : D --> D )

  proof
    cD
    cV
    wcel
    #
    cP
    cD
    wss
    #
    cP
    c2o
    cen
    wbr
    #
    w3a
    #
    cD
    cD
    cP
    cT
    cfv
    #
    wf
    cD
    cD
    vz
    cD
    vz
    cv
    #
    cP
    wcel
    #
    cP
    @5
    csn
    #
    cdif
    #
    cuni
    #
    @5
    cif
    #
    cmpt
    #
    wf
    @3
    vz
    cD
    @10
    cD
    @11
    @3
    @5
    cD
    wcel
    #
    wa
    #
    @6
    @9
    @5
    cD
    @13
    @6
    wa
    #
    cP
    cD
    @9
    @0
    @1
    @2
    @12
    @6
    simpll2
    @14
    @8
    c1o
    cen
    wbr
    #
    @9
    @8
    wcel
    @9
    cP
    wcel
    @14
    c1o
    com
    wcel
    #
    cP
    c1o
    csuc
    #
    cen
    wbr
    @6
    @15
    @16
    @14
    1onn
    a1i
    @14
    cP
    c2o
    @17
    cen
    @0
    @1
    @2
    @12
    @6
    simpll3
    df-2o
    syl6breq
    @13
    @6
    simpr
    cP
    c1o
    @5
    dif1en
    syl3anc
    @8
    en1uniel
    @9
    cP
    @7
    eldifi
    3syl
    sseldd
    @3
    @12
    @6
    wn
    simplr
    ifclda
    @11
    eqid
    fmptd
    @3
    cD
    cD
    @4
    @11
    vz
    cD
    cP
    cT
    cV
    pmtrfval.t
    pmtrval
    feq1d
    mpbird
end
