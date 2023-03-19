include "wfn.mm"
include "ccnv.mm"
include "wf1o.mm"
include "wf.mm"
include "cgrp.mm"
include "wcel.mm"
include "grpinvf.mm"
include "syl.mm"
include "ffn.mm"
include "wceq.mm"
include "grpinvcnv.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "dff1o4.mm"
include "sylanbrc.mm"

theorem grpinvf1o
  let wph: wff ph
  let cB: class B
  let cG: class G
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume grpinvinv.b: |- B = ( Base ` G )
  assume grpinvinv.n: |- N = ( invg ` G )
  assume grpinv11.g: |- ( ph -> G e. Grp )


  assert |- ( ph -> N : B -1-1-onto-> B )

  proof
    wph
    cN
    cB
    wfn
    #
    cN
    ccnv
    #
    cB
    wfn
    #
    cB
    cB
    cN
    wf1o
    wph
    cB
    cB
    cN
    wf
    #
    @0
    wph
    cG
    cgrp
    wcel
    #
    @3
    grpinv11.g
    cB
    cG
    cN
    grpinvinv.b
    grpinvinv.n
    grpinvf
    syl
    cB
    cB
    cN
    ffn
    syl
    #
    wph
    @2
    @0
    @5
    wph
    cB
    @1
    cN
    wph
    @4
    @1
    cN
    wceq
    grpinv11.g
    cB
    cG
    cN
    grpinvinv.b
    grpinvinv.n
    grpinvcnv
    syl
    fneq1d
    mpbird
    cB
    cB
    cN
    dff1o4
    sylanbrc
end
