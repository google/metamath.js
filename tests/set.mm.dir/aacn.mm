include "caa.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "cply.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "elaa.mm"
include "simplbi.mm"

theorem aacn
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let cP: class P
  let wph: wff ph
  let cF: class F
  let cK: class K
  let cN: class N
  let cR: class R


  assert |- ( A e. AA -> A e. CC )

  proof
    cA
    caa
    wcel
    cA
    cc
    wcel
    cA
    vf
    cv
    cfv
    cc0
    wceq
    vf
    cz
    cply
    cfv
    c0p
    csn
    cdif
    wrex
    cA
    vf
    elaa
    simplbi
end
