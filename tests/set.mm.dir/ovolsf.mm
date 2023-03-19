include "cn.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "nnuz.mm"
include "1zzd.mm"
include "cv.mm"
include "ovolfsf.mm"
include "ffvelrnda.mm"
include "wcel.mm"
include "wa.mm"
include "ge0addcl.mm"
include "adantl.mm"
include "seqf.mm"
include "feq1i.mm"
include "sylibr.mm"

theorem ovolsf
  let cS: class S
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  assume ovolfs.1: |- G = ( ( abs o. - ) o. F )
  assume ovolfs.2: |- S = seq 1 ( + , G )


  assert |- ( F : NN --> ( <_ i^i ( RR X. RR ) ) -> S : NN --> ( 0 [,) +oo ) )

  proof
    cn
    cle
    cr
    cr
    cxp
    cin
    cF
    wf
    #
    cn
    cc0
    cpnf
    cico
    co
    #
    caddc
    cG
    c1
    cseq
    #
    wf
    cn
    @1
    cS
    wf
    @0
    vx
    vy
    caddc
    @1
    cG
    c1
    cn
    nnuz
    @0
    1zzd
    @0
    cn
    @1
    vx
    cv
    #
    cG
    cF
    cG
    ovolfs.1
    ovolfsf
    ffvelrnda
    @3
    @1
    wcel
    vy
    cv
    #
    @1
    wcel
    wa
    @3
    @4
    caddc
    co
    @1
    wcel
    @0
    @3
    @4
    ge0addcl
    adantl
    seqf
    cn
    @1
    cS
    @2
    ovolfs.2
    feq1i
    sylibr
end
