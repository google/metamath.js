include "coppg.mm"
include "cfv.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "eqid.mm"
include "cgrp.mm"
include "wcel.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "syl.mm"
include "wf.mm"
include "grpinvf.mm"
include "fco.mm"
include "syl2anc.mm"
include "crn.mm"
include "cima.mm"
include "ccntz.mm"
include "cmhm.mm"
include "wss.mm"
include "cgim.mm"
include "cghm.mm"
include "invoppggim.mm"
include "gimghm.mm"
include "ghmmhm.mm"
include "4syl.mm"
include "cntzmhm2.mm"
include "rnco2.mm"
include "fveq2i.mm"
include "oppgcntz.mm"
include "eqtri.mm"
include "3sstr4g.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cbs.mm"
include "wceq.mm"
include "grpinvid.mm"
include "fsuppco2.mm"
include "gsumzoppg.mm"
include "oppgmnd.mm"
include "gsumzmhm.mm"
include "eqtr3d.mm"

theorem gsumzinv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  assume gsumzinv.b: |- B = ( Base ` G )
  assume gsumzinv.0: |- .0. = ( 0g ` G )
  assume gsumzinv.z: |- Z = ( Cntz ` G )
  assume gsumzinv.i: |- I = ( invg ` G )
  assume gsumzinv.g: |- ( ph -> G e. Grp )
  assume gsumzinv.a: |- ( ph -> A e. V )
  assume gsumzinv.f: |- ( ph -> F : A --> B )
  assume gsumzinv.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumzinv.n: |- ( ph -> F finSupp .0. )


  assert |- ( ph -> ( G gsum ( I o. F ) ) = ( I ` ( G gsum F ) ) )

  proof
    wph
    cG
    coppg
    cfv
    #
    cI
    cF
    ccom
    #
    cgsu
    co
    cG
    @1
    cgsu
    co
    cG
    cF
    cgsu
    co
    cI
    cfv
    wph
    cA
    cB
    @1
    cG
    @0
    cV
    c.0
    cZ
    gsumzinv.b
    gsumzinv.0
    gsumzinv.z
    @0
    eqid
    #
    wph
    cG
    cgrp
    wcel
    #
    cG
    cmnd
    wcel
    #
    gsumzinv.g
    cG
    grpmnd
    syl
    #
    gsumzinv.a
    wph
    cB
    cB
    cI
    wf
    #
    cA
    cB
    cF
    wf
    cA
    cB
    @1
    wf
    wph
    @3
    @6
    gsumzinv.g
    cB
    cG
    cI
    gsumzinv.b
    gsumzinv.i
    grpinvf
    syl
    #
    gsumzinv.f
    cA
    cB
    cB
    cI
    cF
    fco
    syl2anc
    wph
    cI
    cF
    crn
    #
    cima
    #
    @9
    @0
    ccntz
    cfv
    #
    cfv
    #
    @1
    crn
    #
    @12
    cZ
    cfv
    #
    wph
    cI
    cG
    @0
    cmhm
    co
    wcel
    #
    @8
    @8
    cZ
    cfv
    wss
    @9
    @11
    wss
    wph
    @3
    cI
    cG
    @0
    cgim
    co
    wcel
    cI
    cG
    @0
    cghm
    co
    wcel
    @14
    gsumzinv.g
    cG
    cI
    @0
    @2
    gsumzinv.i
    invoppggim
    cG
    @0
    cI
    gimghm
    cG
    @0
    cI
    ghmmhm
    4syl
    #
    gsumzinv.c
    @8
    @8
    cI
    cG
    @0
    @10
    cZ
    gsumzinv.z
    @10
    eqid
    cntzmhm2
    syl2anc
    cI
    cF
    rnco2
    #
    @13
    @9
    cZ
    cfv
    @11
    @12
    @9
    cZ
    @16
    fveq2i
    @9
    cG
    @0
    cZ
    @2
    gsumzinv.z
    oppgcntz
    eqtri
    3sstr4g
    wph
    cA
    cB
    cV
    cF
    cI
    cvv
    cvv
    c.0
    c.0
    cvv
    wcel
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsumzinv.0
    cG
    c0g
    fvex
    eqeltri
    a1i
    gsumzinv.f
    @7
    gsumzinv.a
    cB
    cvv
    wcel
    wph
    cB
    cG
    cbs
    cfv
    cvv
    gsumzinv.b
    cG
    cbs
    fvex
    eqeltri
    a1i
    gsumzinv.n
    wph
    @3
    c.0
    cI
    cfv
    c.0
    wceq
    gsumzinv.g
    cG
    cI
    c.0
    gsumzinv.0
    gsumzinv.i
    grpinvid
    syl
    fsuppco2
    gsumzoppg
    wph
    cA
    cB
    cF
    cG
    @0
    cI
    cV
    c.0
    cZ
    gsumzinv.b
    gsumzinv.z
    @5
    wph
    @4
    @0
    cmnd
    wcel
    @5
    cG
    @0
    @2
    oppgmnd
    syl
    gsumzinv.a
    @15
    gsumzinv.f
    gsumzinv.c
    gsumzinv.0
    gsumzinv.n
    gsumzmhm
    eqtr3d
end
