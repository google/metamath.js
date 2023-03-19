include "cr.mm"
include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cres.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wf.mm"
include "cc.mm"
include "plybss.mm"
include "wb.mm"
include "plyf.mm"
include "ffn.mm"
include "fnssresb.mm"
include "3syl.mm"
include "mpbird.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "fvres.mm"
include "adantl.mm"
include "recn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "ccj.mm"
include "plyrecj.mm"
include "sylan2.mm"
include "cjre.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "cjrebd.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "df-f.mm"
include "sylanbrc.mm"

theorem plyreres
  let cF: class F
  let va: setvar a


  assert |- ( F e. ( Poly ` RR ) -> ( F |` RR ) : RR --> RR )

  proof
    cF
    cr
    cply
    cfv
    wcel
    #
    cF
    cr
    cres
    #
    cr
    wfn
    #
    @1
    crn
    cr
    wss
    #
    cr
    cr
    @1
    wf
    @0
    @2
    cr
    cc
    wss
    #
    cr
    cF
    plybss
    @0
    cc
    cc
    cF
    wf
    #
    cF
    cc
    wfn
    @2
    @4
    wb
    cr
    cF
    plyf
    #
    cc
    cc
    cF
    ffn
    cc
    cr
    cF
    fnssresb
    3syl
    mpbird
    #
    @0
    @2
    va
    cv
    #
    @1
    cfv
    #
    cr
    wcel
    #
    va
    cr
    wral
    @3
    @7
    @0
    @10
    va
    cr
    @0
    @8
    cr
    wcel
    #
    wa
    #
    @9
    @8
    cF
    cfv
    #
    cr
    @11
    @9
    @13
    wceq
    @0
    @8
    cr
    cF
    fvres
    adantl
    @12
    @13
    @0
    @5
    @8
    cc
    wcel
    #
    @13
    cc
    wcel
    @11
    @6
    @8
    recn
    #
    cc
    cc
    @8
    cF
    ffvelrn
    syl2an
    @12
    @13
    ccj
    cfv
    #
    @8
    ccj
    cfv
    #
    cF
    cfv
    #
    @13
    @11
    @0
    @14
    @16
    @18
    wceq
    @15
    @8
    cF
    plyrecj
    sylan2
    @12
    @17
    @8
    cF
    @11
    @17
    @8
    wceq
    @0
    @8
    cjre
    adantl
    fveq2d
    eqtrd
    cjrebd
    eqeltrd
    ralrimiva
    va
    cr
    cr
    @1
    fnfvrnss
    syl2anc
    cr
    cr
    @1
    df-f
    sylanbrc
end
